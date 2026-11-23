# Dafny Storage & Indexing Internals Module

Formally verified Dafny 4 models of three foundational database storage and indexing structures:

1. **B+ Tree (`BPlusTree.dfy`)**
   - Uniform-depth balanced tree invariant (`ValidNode`, `ValidBPlusTree`) with strict key ordering and exact separator-key routing bounds (`keys[i-1] <= k < keys[i]`).
   - Verified `Search`, sorted `RangeScan(tree, lo, hi)`, and `Insert` implementing both **Leaf Copy-Up Splits** and **Internal Push-Up Splits** (with root height growth).
2. **Extendible Hashing (`ExtendibleHashing.dfy`)**
   - Dynamic hash directory (`2^globalDepth` pointers) and buckets with `localDepth <= globalDepth` and verified hash-suffix consistency (`ValidExtHash`).
   - Verified `Lookup`, `DoubleDirectory`, `SplitBucket`, and `Insert` (with guaranteed termination via `maxDepth - localDepth`).
3. **LSM-Tree (`LsmTree.dfy`)**
   - Sorted in-memory `memtable` supporting `Put` and `Tombstone` deletes, automatic flush to immutable L0 SSTables, and verified two-pointer `MergeRuns(newer, older)`.
   - `CompactAll(lsm)` merges all SSTables and garbage-collects bottom-level tombstones while formally proving `forall k :: Get(compacted, k) == Get(lsm, k)`.

## Files

- [dfyconfig.toml](dfyconfig.toml) — Dafny 4 project configuration.
- [Types.dfy](Types.dfy) — Shared `Key`, `Value`, `Entry`, `Option<T>`, sorted-entry helpers, and `Pow2`.
- [BPlusTree.dfy](BPlusTree.dfy) — `module BPlusTreeIndex`.
- [ExtendibleHashing.dfy](ExtendibleHashing.dfy) — `module ExtendibleHashingIndex`.
- [LsmTree.dfy](LsmTree.dfy) — `module LsmTreeIndex`.
- [Main.dfy](Main.dfy) — Statically verified tests and runnable demos.
