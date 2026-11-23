// Formally Verified LSM-Tree (Log-Structured Merge-Tree) Storage Engine (`LsmTreeIndex`).
//
// Models a write-optimized LSM-Tree (as used in RocksDB / LevelDB / Cassandra):
//   - `memtable`: sorted in-memory write buffer supporting `Put(k, v)` and
//     `Tombstone(k)` deletes.
//   - `sstables`: sequence of immutable sorted SSTable runs on disk ordered
//     newest-to-oldest (`sstables[0]` is newest L0).
//   - Auto-flushes `memtable` into `sstables` when `|memtable| >= memLimit`.
//   - Verified `MergeRuns(newer, older)` two-pointer sorted merge where `newer`
//     shadows `older` on equal keys, and verified `CompactAll(lsm)` proving
//     that full compaction preserves `Get(lsm, k)` for EVERY key `k`!

include "Types.dfy"

module LsmTreeIndex {
  import opened IndexingTypes

  datatype LsmEntry =
    | LsmPut(key: Key, val: Value)
    | LsmTombstone(key: Key)

  datatype LsmTree = LsmTree(
    memLimit: nat,
    memtable: seq<LsmEntry>,
    sstables: seq<seq<LsmEntry>>
  )

  predicate LsmRunSorted(run: seq<LsmEntry>)
  {
    forall i, j :: 0 <= i < j < |run| ==> run[i].key < run[j].key
  }

  predicate ValidLsmTree(lsm: LsmTree)
  {
    lsm.memLimit >= 1 &&
    LsmRunSorted(lsm.memtable) &&
    (forall i :: 0 <= i < |lsm.sstables| ==> LsmRunSorted(lsm.sstables[i]))
  }

  function EmptyLsmTree(memLimit: nat): LsmTree
    requires memLimit >= 1
    ensures ValidLsmTree(EmptyLsmTree(memLimit))
  {
    LsmTree(memLimit, [], [])
  }

  // ---------------------------------------------------------------------------
  // Sorted Run Lookup & Upsert
  // ---------------------------------------------------------------------------

  function LookupRun(run: seq<LsmEntry>, k: Key): Option<LsmEntry>
    decreases |run|
  {
    if |run| == 0 then None
    else if run[0].key == k then Some(run[0])
    else LookupRun(run[1..], k)
  }

  lemma LemmaLookupRunBelowHead(run: seq<LsmEntry>, k: Key)
    requires LsmRunSorted(run)
    requires |run| > 0 && k < run[0].key
    ensures LookupRun(run, k) == None
    decreases |run|
  {
    if |run| > 1 {
      LemmaLookupRunBelowHead(run[1..], k);
    }
  }

  function LookupRuns(runs: seq<seq<LsmEntry>>, k: Key): Option<LsmEntry>
    decreases |runs|
  {
    if |runs| == 0 then None
    else
      var hit := LookupRun(runs[0], k);
      if hit.Some? then hit else LookupRuns(runs[1..], k)
  }

  // Resolves a key across `memtable` (newest) followed by `sstables` (newest to oldest).
  function Get(lsm: LsmTree, k: Key): Option<Value>
  {
    var hit := LookupRun(lsm.memtable, k);
    var entryOpt := if hit.Some? then hit else LookupRuns(lsm.sstables, k);
    match entryOpt
    case None => None
    case Some(LsmPut(_, v)) => Some(v)
    case Some(LsmTombstone(_)) => None
  }

  function UpsertLsmEntry(run: seq<LsmEntry>, entry: LsmEntry): seq<LsmEntry>
    requires LsmRunSorted(run)
    ensures LsmRunSorted(UpsertLsmEntry(run, entry))
    ensures LookupRun(UpsertLsmEntry(run, entry), entry.key) == Some(entry)
    ensures forall k :: k != entry.key ==>
      LookupRun(UpsertLsmEntry(run, entry), k) == LookupRun(run, k)
    decreases |run|
  {
    if |run| == 0 then
      [entry]
    else if entry.key < run[0].key then
      [entry] + run
    else if entry.key == run[0].key then
      [entry] + run[1..]
    else
      [run[0]] + UpsertLsmEntry(run[1..], entry)
  }

  // ---------------------------------------------------------------------------
  // Write Path: Put, Delete (Tombstone), and Memtable Flush to L0 SSTable
  // ---------------------------------------------------------------------------

  function FlushMemtable(lsm: LsmTree): LsmTree
    requires ValidLsmTree(lsm)
    ensures ValidLsmTree(FlushMemtable(lsm))
    ensures forall k :: Get(FlushMemtable(lsm), k) == Get(lsm, k)
  {
    if |lsm.memtable| == 0 then
      lsm
    else
      LsmTree(lsm.memLimit, [], [lsm.memtable] + lsm.sstables)
  }

  function ApplyWrite(lsm: LsmTree, entry: LsmEntry): LsmTree
    requires ValidLsmTree(lsm)
    ensures ValidLsmTree(ApplyWrite(lsm, entry))
    ensures forall k :: k != entry.key ==> Get(ApplyWrite(lsm, entry), k) == Get(lsm, k)
  {
    var nextMem := UpsertLsmEntry(lsm.memtable, entry);
    var updated := LsmTree(lsm.memLimit, nextMem, lsm.sstables);
    if |nextMem| >= lsm.memLimit then
      FlushMemtable(updated)
    else
      updated
  }

  function Put(lsm: LsmTree, k: Key, v: Value): LsmTree
    requires ValidLsmTree(lsm)
    ensures ValidLsmTree(Put(lsm, k, v))
    ensures Get(Put(lsm, k, v), k) == Some(v)
    ensures forall other :: other != k ==> Get(Put(lsm, k, v), other) == Get(lsm, other)
  {
    ApplyWrite(lsm, LsmPut(k, v))
  }

  function Delete(lsm: LsmTree, k: Key): LsmTree
    requires ValidLsmTree(lsm)
    ensures ValidLsmTree(Delete(lsm, k))
    ensures Get(Delete(lsm, k), k) == None
    ensures forall other :: other != k ==> Get(Delete(lsm, k), other) == Get(lsm, other)
  {
    ApplyWrite(lsm, LsmTombstone(k))
  }

  // ---------------------------------------------------------------------------
  // Compaction: Verified Two-Pointer Sorted Merge & Bottom-Level Tombstone GC
  // ---------------------------------------------------------------------------

  // Merges two sorted SSTable runs (`newer` takes precedence over `older` on equal keys).
  function MergeRuns(newer: seq<LsmEntry>, older: seq<LsmEntry>): seq<LsmEntry>
    requires LsmRunSorted(newer) && LsmRunSorted(older)
    ensures LsmRunSorted(MergeRuns(newer, older))
    ensures forall i :: 0 <= i < |MergeRuns(newer, older)| ==>
      MergeRuns(newer, older)[i] in newer || MergeRuns(newer, older)[i] in older
    decreases |newer| + |older|
  {
    if |newer| == 0 then
      older
    else if |older| == 0 then
      newer
    else if newer[0].key < older[0].key then
      [newer[0]] + MergeRuns(newer[1..], older)
    else if newer[0].key == older[0].key then
      [newer[0]] + MergeRuns(newer[1..], older[1..])
    else
      [older[0]] + MergeRuns(newer, older[1..])
  }

  // Formal Semantic Preservation Theorem for SSTable Merge:
  // Looking up any key `k` in `MergeRuns(newer, older)` yields the exact same
  // result as checking `newer` first and falling back to `older`!
  lemma LemmaMergeRunsLookupEquiv(newer: seq<LsmEntry>, older: seq<LsmEntry>, k: Key)
    requires LsmRunSorted(newer) && LsmRunSorted(older)
    ensures LookupRun(MergeRuns(newer, older), k) ==
            (if LookupRun(newer, k).Some? then LookupRun(newer, k) else LookupRun(older, k))
    decreases |newer| + |older|
  {
    if |newer| == 0 || |older| == 0 {
    } else if newer[0].key < older[0].key {
      if k == newer[0].key {
      } else {
        LemmaMergeRunsLookupEquiv(newer[1..], older, k);
      }
    } else if newer[0].key == older[0].key {
      if k == newer[0].key {
      } else {
        LemmaMergeRunsLookupEquiv(newer[1..], older[1..], k);
      }
    } else {
      if k == older[0].key {
        LemmaLookupRunBelowHead(newer, k);
      } else {
        LemmaMergeRunsLookupEquiv(newer, older[1..], k);
      }
    }
  }

  // Drops tombstones when compacting to the bottommost level (no older runs remain).
  function DropTombstones(run: seq<LsmEntry>): seq<LsmEntry>
    requires LsmRunSorted(run)
    ensures LsmRunSorted(DropTombstones(run))
    ensures forall i :: 0 <= i < |DropTombstones(run)| ==>
      DropTombstones(run)[i] in run && DropTombstones(run)[i].LsmPut?
    decreases |run|
  {
    if |run| == 0 then []
    else if run[0].LsmTombstone? then DropTombstones(run[1..])
    else [run[0]] + DropTombstones(run[1..])
  }

  lemma LemmaDropTombstonesGetEquiv(run: seq<LsmEntry>, k: Key)
    requires LsmRunSorted(run)
    ensures (match LookupRun(DropTombstones(run), k)
             case None => None
             case Some(LsmPut(_, v)) => Some(v)
             case Some(LsmTombstone(_)) => None) ==
            (match LookupRun(run, k)
             case None => None
             case Some(LsmPut(_, v)) => Some(v)
             case Some(LsmTombstone(_)) => None)
    decreases |run|
  {
    if |run| == 0 {
    } else if run[0].LsmTombstone? {
      if k == run[0].key {
        LemmaDropTombstonesBelowHead(run[1..], k);
      } else {
        LemmaDropTombstonesGetEquiv(run[1..], k);
      }
    } else {
      if k == run[0].key {
      } else {
        LemmaDropTombstonesGetEquiv(run[1..], k);
      }
    }
  }

  lemma LemmaDropTombstonesBelowHead(run: seq<LsmEntry>, k: Key)
    requires LsmRunSorted(run)
    requires forall i :: 0 <= i < |run| ==> k < run[i].key
    ensures LookupRun(DropTombstones(run), k) == None
    decreases |run|
  {
    if |run| > 0 {
      LemmaDropTombstonesBelowHead(run[1..], k);
    }
  }

  // Folds all SSTables newest-to-oldest into a single merged sorted run.
  function MergeAllRuns(runs: seq<seq<LsmEntry>>): seq<LsmEntry>
    requires forall i :: 0 <= i < |runs| ==> LsmRunSorted(runs[i])
    ensures LsmRunSorted(MergeAllRuns(runs))
    decreases |runs|
  {
    if |runs| == 0 then []
    else MergeRuns(runs[0], MergeAllRuns(runs[1..]))
  }

  lemma LemmaMergeAllRunsLookupEquiv(runs: seq<seq<LsmEntry>>, k: Key)
    requires forall i :: 0 <= i < |runs| ==> LsmRunSorted(runs[i])
    ensures LookupRun(MergeAllRuns(runs), k) == LookupRuns(runs, k)
    decreases |runs|
  {
    if |runs| == 0 {
    } else {
      LemmaMergeAllRunsLookupEquiv(runs[1..], k);
      LemmaMergeRunsLookupEquiv(runs[0], MergeAllRuns(runs[1..]), k);
    }
  }

  // Full Compaction: merges all SSTables into one sorted run and garbage-collects
  // tombstones at the bottommost level, formally preserving `Get(lsm, k)` for all keys!
  method CompactAll(lsm: LsmTree) returns (compacted: LsmTree)
    requires ValidLsmTree(lsm)
    ensures ValidLsmTree(compacted)
    ensures |compacted.sstables| <= 1
    ensures forall k :: Get(compacted, k) == Get(lsm, k)
  {
    var merged := MergeAllRuns(lsm.sstables);
    var cleaned := DropTombstones(merged);
    if |cleaned| == 0 {
      compacted := LsmTree(lsm.memLimit, lsm.memtable, []);
    } else {
      compacted := LsmTree(lsm.memLimit, lsm.memtable, [cleaned]);
    }

    forall k
      ensures Get(compacted, k) == Get(lsm, k)
    {
      LemmaMergeAllRunsLookupEquiv(lsm.sstables, k);
      LemmaDropTombstonesGetEquiv(merged, k);
    }
  }
}
