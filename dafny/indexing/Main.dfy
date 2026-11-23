// Statically verified tests and runnable demonstrations for the Storage &
// Indexing Internals module (`dafny/indexing/`):
//   1. `TestBPlusTreeVerified` — tests B+ Tree insertion with leaf copy-up
//      splits, internal push-up splits, height growth, search, and range scans.
//   2. `TestExtendibleHashingVerified` — tests dynamic Extendible Hashing with
//      bucket splitting, directory doubling, and verified lookups.
//   3. `TestLsmTreeVerified` — tests LSM-Tree memtable writes, tombstones,
//      auto-flushing to L0 SSTables, and full compaction with verified `Get`
//      preservation across all keys.

include "Types.dfy"
include "BPlusTree.dfy"
include "ExtendibleHashing.dfy"
include "LsmTree.dfy"

module Main {
  import opened IndexingTypes
  import BPlusTreeIndex
  import ExtendibleHashingIndex
  import LsmTreeIndex

  // 1. B+ Tree: Insertions triggering leaf copy-up split, internal push-up split & range scan
  method TestBPlusTreeVerified()
  {
    var t := BPlusTreeIndex.EmptyBPlusTree(2);
    assert BPlusTreeIndex.ValidBPlusTree(t);
    assert t.height == 0;

    t := BPlusTreeIndex.Insert(t, 10, 100);
    t := BPlusTreeIndex.Insert(t, 20, 200);
    t := BPlusTreeIndex.Insert(t, 30, 300); // Triggers leaf copy-up split + root split (height = 1)
    t := BPlusTreeIndex.Insert(t, 40, 400);
    t := BPlusTreeIndex.Insert(t, 50, 500);
    t := BPlusTreeIndex.Insert(t, 25, 250);
    t := BPlusTreeIndex.Insert(t, 15, 150);
    assert BPlusTreeIndex.ValidBPlusTree(t);

    var hit25 := BPlusTreeIndex.Search(t, 25);
    var range := BPlusTreeIndex.RangeScan(t, 15, 40);
    assert EntriesStrictlySorted(range);
    assert forall i :: 0 <= i < |range| ==> 15 <= range[i].key <= 40;

    print "=== 1. B+ Tree (maxKeys=2) Verified ===\n";
    print "Height after 7 inserts: ", t.height, "\n";
    print "Search(25) = ", hit25, "\n";
    print "RangeScan([15, 40]) count = ", |range|, "\n\n";
  }

  // 2. Extendible Hashing: Bucket splitting & directory doubling
  method TestExtendibleHashingVerified()
  {
    var eh := ExtendibleHashingIndex.EmptyExtHash(2, 4);
    assert ExtendibleHashingIndex.ValidExtHash(eh);

    var ok: bool;
    eh, ok := ExtendibleHashingIndex.Insert(eh, 4, 40);   // 4 mod 1 = 0
    assert ok && ExtendibleHashingIndex.Lookup(eh, 4) == Some(40);
    eh, ok := ExtendibleHashingIndex.Insert(eh, 5, 50);   // 5 mod 1 = 0 (bucket full)
    assert ok && ExtendibleHashingIndex.Lookup(eh, 5) == Some(50);
    eh, ok := ExtendibleHashingIndex.Insert(eh, 6, 60);   // Doubles directory (gd=1) + splits bucket!
    assert ok && ExtendibleHashingIndex.Lookup(eh, 6) == Some(60);
    eh, ok := ExtendibleHashingIndex.Insert(eh, 7, 70);
    assert ok && ExtendibleHashingIndex.Lookup(eh, 7) == Some(70);
    eh, ok := ExtendibleHashingIndex.Insert(eh, 8, 80);   // Doubles directory (gd=2) + splits bucket!
    assert ok && ExtendibleHashingIndex.Lookup(eh, 8) == Some(80);
    assert ExtendibleHashingIndex.ValidExtHash(eh);

    print "=== 2. Extendible Hashing (capacity=2) Verified ===\n";
    print "Global depth: ", eh.globalDepth, ", directory slots: ", |eh.directory|, ", buckets: ", |eh.buckets|, "\n";
    print "Lookup(6) = ", ExtendibleHashingIndex.Lookup(eh, 6), "\n\n";
  }

  // 3. LSM-Tree: Memtable writes, tombstone deletes, auto-flush, and verified compaction
  method TestLsmTreeVerified()
  {
    var lsm := LsmTreeIndex.EmptyLsmTree(2);
    assert LsmTreeIndex.ValidLsmTree(lsm);

    lsm := LsmTreeIndex.Put(lsm, 10, 100);
    lsm := LsmTreeIndex.Put(lsm, 20, 200); // Flushes to SSTable #1
    assert LsmTreeIndex.Get(lsm, 10) == Some(100);
    assert LsmTreeIndex.Get(lsm, 20) == Some(200);

    lsm := LsmTreeIndex.Put(lsm, 10, 111); // Newer overwrite of key 10
    lsm := LsmTreeIndex.Delete(lsm, 20);   // Tombstone delete of key 20 -> flushes to SSTable #2
    assert LsmTreeIndex.Get(lsm, 10) == Some(111);
    assert LsmTreeIndex.Get(lsm, 20) == None;

    lsm := LsmTreeIndex.Put(lsm, 30, 300);
    assert LsmTreeIndex.Get(lsm, 30) == Some(300);

    var compacted := LsmTreeIndex.CompactAll(lsm);
    assert LsmTreeIndex.ValidLsmTree(compacted);
    assert |compacted.sstables| <= 1;
    // Formally proved by CompactAll's postcondition for ALL keys!
    assert LsmTreeIndex.Get(compacted, 10) == Some(111);
    assert LsmTreeIndex.Get(compacted, 20) == None;
    assert LsmTreeIndex.Get(compacted, 30) == Some(300);

    print "=== 3. LSM-Tree (memLimit=2) Verified ===\n";
    print "SSTables before compaction: ", |lsm.sstables|, ", after compaction: ", |compacted.sstables|, "\n";
    print "Get(10) = ", LsmTreeIndex.Get(compacted, 10), ", Get(20) = ", LsmTreeIndex.Get(compacted, 20), ", Get(30) = ", LsmTreeIndex.Get(compacted, 30), "\n";
  }

  method Main()
  {
    TestBPlusTreeVerified();
    TestExtendibleHashingVerified();
    TestLsmTreeVerified();
  }
}
