// Formally Verified Extendible Hashing Index (`ExtendibleHashingIndex`).
//
// Models dynamic Extendible Hashing with:
//   - A directory of `2^globalDepth` bucket pointers (`directory: seq<nat>`).
//   - Buckets with `localDepth <= globalDepth`, capacity limit, and strictly
//     sorted entries matching the bucket's `localDepth`-bit hash suffix.
//   - Verified `Lookup`, `DoubleDirectory` (`globalDepth -> globalDepth + 1`),
//     `SplitBucket` (`localDepth -> localDepth + 1` with entry redistribution
//     and directory pointer rewiring), and `Insert`.

include "Types.dfy"

module ExtendibleHashingIndex {
  import opened IndexingTypes

  datatype HashBucket = HashBucket(
    localDepth: nat,
    suffix: nat,
    entries: seq<Entry>
  )

  datatype ExtHash = ExtHash(
    globalDepth: nat,
    maxDepth: nat,
    capacity: nat,
    directory: seq<nat>,
    buckets: seq<HashBucket>
  )

  function AbsKey(k: Key): nat
  {
    if k >= 0 then k else -k
  }

  function HashMod(k: Key, depth: nat): nat
    ensures HashMod(k, depth) < Pow2(depth)
  {
    AbsKey(k) % Pow2(depth)
  }

  // ---------------------------------------------------------------------------
  // Modular Arithmetic Lemmas for Powers of Two
  // ---------------------------------------------------------------------------

  lemma LemmaPow2Monotonic(a: nat, b: nat)
    requires a <= b
    ensures Pow2(a) <= Pow2(b)
    decreases b - a
  {
    if a < b {
      LemmaPow2Monotonic(a, b - 1);
    }
  }

  lemma LemmaPow2Factor(a: nat, b: nat)
    requires a <= b
    ensures exists m: nat :: m >= 1 && Pow2(b) == m * Pow2(a)
    decreases b - a
  {
    if a == b {
      assert Pow2(b) == 1 * Pow2(a);
    } else {
      LemmaPow2Factor(a, b - 1);
      var m :| m >= 1 && Pow2(b - 1) == m * Pow2(a);
      assert Pow2(b) == (2 * m) * Pow2(a);
    }
  }

  lemma LemmaModMultipleAdd(x: nat, k: nat, p: nat)
    requires p >= 1
    ensures (x + k * p) % p == x % p
  {
    var q := x / p;
    var r := x % p;
    assert x == q * p + r && 0 <= r < p;
    assert x + k * p == (q + k) * p + r;
    assert (x + k * p) % p == r;
  }

  lemma LemmaModPow2AddHigher(x: nat, ld: nat, gd: nat)
    requires ld <= gd
    ensures (x + Pow2(gd)) % Pow2(ld) == x % Pow2(ld)
  {
    LemmaPow2Factor(ld, gd);
    var m :| m >= 1 && Pow2(gd) == m * Pow2(ld);
    LemmaModMultipleAdd(x, m, Pow2(ld));
  }

  lemma LemmaNextBitSplit(x: nat, ld: nat)
    ensures x % Pow2(ld + 1) == x % Pow2(ld) ||
            x % Pow2(ld + 1) == x % Pow2(ld) + Pow2(ld)
  {
    var p := Pow2(ld);
    var p2 := Pow2(ld + 1);
    assert p2 == 2 * p;
    var r2 := x % p2;
    var q2 := x / p2;
    assert x == q2 * (2 * p) + r2 && 0 <= r2 < 2 * p;
    if r2 < p {
      assert x == (2 * q2) * p + r2;
      assert x % p == r2;
    } else {
      var rem := r2 - p;
      assert 0 <= rem < p;
      assert x == (2 * q2 + 1) * p + rem;
      assert x % p == rem;
      assert r2 == rem + p;
    }
  }

  // ---------------------------------------------------------------------------
  // Extendible Hashing Invariant
  // ---------------------------------------------------------------------------

  predicate ValidBucket(b: HashBucket, globalDepth: nat, capacity: nat)
  {
    b.localDepth <= globalDepth &&
    b.suffix < Pow2(b.localDepth) &&
    |b.entries| <= capacity &&
    EntriesStrictlySorted(b.entries) &&
    (forall j :: 0 <= j < |b.entries| ==>
      HashMod(b.entries[j].key, b.localDepth) == b.suffix)
  }

  predicate ValidExtHash(eh: ExtHash)
  {
    eh.capacity >= 1 &&
    eh.globalDepth <= eh.maxDepth &&
    |eh.directory| == Pow2(eh.globalDepth) &&
    (forall b :: 0 <= b < |eh.buckets| ==>
      ValidBucket(eh.buckets[b], eh.globalDepth, eh.capacity)) &&
    (forall d :: 0 <= d < |eh.directory| ==>
      eh.directory[d] < |eh.buckets| &&
      var b := eh.buckets[eh.directory[d]];
      d % Pow2(b.localDepth) == b.suffix)
  }

  function EmptyExtHash(capacity: nat, maxDepth: nat): ExtHash
    requires capacity >= 1
    ensures ValidExtHash(EmptyExtHash(capacity, maxDepth))
  {
    ExtHash(0, maxDepth, capacity, [0], [HashBucket(0, 0, [])])
  }

  // ---------------------------------------------------------------------------
  // Lookup
  // ---------------------------------------------------------------------------

  function Lookup(eh: ExtHash, k: Key): Option<Value>
    requires ValidExtHash(eh)
  {
    var dirIdx := HashMod(k, eh.globalDepth);
    var bIdx := eh.directory[dirIdx];
    LookupEntries(eh.buckets[bIdx].entries, k)
  }

  // ---------------------------------------------------------------------------
  // Directory Doubling (`globalDepth -> globalDepth + 1`)
  // ---------------------------------------------------------------------------

  method DoubleDirectory(eh: ExtHash) returns (next: ExtHash)
    requires ValidExtHash(eh)
    requires eh.globalDepth < eh.maxDepth
    ensures ValidExtHash(next)
    ensures next.globalDepth == eh.globalDepth + 1
    ensures next.maxDepth == eh.maxDepth
    ensures next.capacity == eh.capacity
    ensures next.buckets == eh.buckets
    ensures next.directory == eh.directory + eh.directory
  {
    var newDir := eh.directory + eh.directory;
    var newGlobal := eh.globalDepth + 1;
    assert |newDir| == Pow2(newGlobal);

    forall d | 0 <= d < |newDir|
      ensures newDir[d] < |eh.buckets| &&
        d % Pow2(eh.buckets[newDir[d]].localDepth) == eh.buckets[newDir[d]].suffix
    {
      if d < |eh.directory| {
        assert newDir[d] == eh.directory[d];
      } else {
        var orig := d - Pow2(eh.globalDepth);
        assert 0 <= orig < |eh.directory|;
        assert newDir[d] == eh.directory[orig];
        var b := eh.buckets[newDir[d]];
        LemmaModPow2AddHigher(orig, b.localDepth, eh.globalDepth);
        assert orig + Pow2(eh.globalDepth) == d;
      }
    }

    next := ExtHash(newGlobal, eh.maxDepth, eh.capacity, newDir, eh.buckets);
  }

  // ---------------------------------------------------------------------------
  // Bucket Splitting (`localDepth -> localDepth + 1`)
  // ---------------------------------------------------------------------------

  function FilterEntriesByHash(
    entries: seq<Entry>,
    depth: nat,
    targetSuffix: nat
  ): seq<Entry>
    requires EntriesStrictlySorted(entries)
    ensures EntriesStrictlySorted(FilterEntriesByHash(entries, depth, targetSuffix))
    ensures |FilterEntriesByHash(entries, depth, targetSuffix)| <= |entries|
    ensures forall i :: 0 <= i < |FilterEntriesByHash(entries, depth, targetSuffix)| ==>
      FilterEntriesByHash(entries, depth, targetSuffix)[i] in entries &&
      HashMod(FilterEntriesByHash(entries, depth, targetSuffix)[i].key, depth) == targetSuffix
    decreases |entries|
  {
    if |entries| == 0 then []
    else
      var rest := FilterEntriesByHash(entries[1..], depth, targetSuffix);
      if HashMod(entries[0].key, depth) == targetSuffix then
        [entries[0]] + rest
      else
        rest
  }

  method SplitBucket(eh: ExtHash, dirIdx: nat) returns (next: ExtHash)
    requires ValidExtHash(eh)
    requires dirIdx < |eh.directory|
    requires eh.buckets[eh.directory[dirIdx]].localDepth < eh.globalDepth
    ensures ValidExtHash(next)
    ensures next.globalDepth == eh.globalDepth
    ensures next.maxDepth == eh.maxDepth
    ensures next.capacity == eh.capacity
    ensures next.buckets[next.directory[dirIdx]].localDepth ==
            eh.buckets[eh.directory[dirIdx]].localDepth + 1
  {
    var bIdx := eh.directory[dirIdx];
    var oldBucket := eh.buckets[bIdx];
    var newLd := oldBucket.localDepth + 1;
    var lowSuffix := oldBucket.suffix;
    var highSuffix := oldBucket.suffix + Pow2(oldBucket.localDepth);

    assert lowSuffix < Pow2(newLd);
    assert highSuffix < Pow2(newLd);

    var lowEntries := FilterEntriesByHash(oldBucket.entries, newLd, lowSuffix);
    var highEntries := FilterEntriesByHash(oldBucket.entries, newLd, highSuffix);

    var lowBucket := HashBucket(newLd, lowSuffix, lowEntries);
    var highBucket := HashBucket(newLd, highSuffix, highEntries);
    var newHighIdx := |eh.buckets|;
    var newBuckets := eh.buckets[bIdx := lowBucket] + [highBucket];

    var newDir := seq(|eh.directory|, d requires 0 <= d < |eh.directory| =>
      if eh.directory[d] == bIdx then
        if d % Pow2(newLd) == lowSuffix then bIdx else newHighIdx
      else
        eh.directory[d]
    );

    forall d | 0 <= d < |newDir|
      ensures newDir[d] < |newBuckets| &&
        d % Pow2(newBuckets[newDir[d]].localDepth) == newBuckets[newDir[d]].suffix
    {
      if eh.directory[d] == bIdx {
        LemmaNextBitSplit(d, oldBucket.localDepth);
        assert d % Pow2(oldBucket.localDepth) == lowSuffix;
        if d % Pow2(newLd) == lowSuffix {
          assert newDir[d] == bIdx;
          assert newBuckets[bIdx] == lowBucket;
        } else {
          assert d % Pow2(newLd) == highSuffix;
          assert newDir[d] == newHighIdx;
          assert newBuckets[newHighIdx] == highBucket;
        }
      } else {
        assert newDir[d] == eh.directory[d];
        assert newBuckets[newDir[d]] == eh.buckets[eh.directory[d]];
      }
    }

    next := ExtHash(eh.globalDepth, eh.maxDepth, eh.capacity, newDir, newBuckets);
  }

  // ---------------------------------------------------------------------------
  // Insert (Upsert with On-Demand Bucket Splitting & Directory Doubling)
  // ---------------------------------------------------------------------------

  method Insert(eh: ExtHash, k: Key, v: Value) returns (next: ExtHash, inserted: bool)
    requires ValidExtHash(eh)
    ensures ValidExtHash(next)
    ensures next.maxDepth == eh.maxDepth
    ensures next.capacity == eh.capacity
    ensures inserted ==> Lookup(next, k) == Some(v)
  {
    next := eh;

    while true
      invariant ValidExtHash(next)
      invariant next.maxDepth == eh.maxDepth
      invariant next.capacity == eh.capacity
      decreases next.maxDepth - next.buckets[next.directory[HashMod(k, next.globalDepth)]].localDepth
    {
      var dirIdx := HashMod(k, next.globalDepth);
      var bIdx := next.directory[dirIdx];
      var bucket := next.buckets[bIdx];

      var updatedEntries := UpsertSortedEntry(bucket.entries, k, v);
      if |updatedEntries| <= next.capacity {
        LemmaModPow2AddHigher(AbsKey(k), bucket.localDepth, next.globalDepth);
        // Show HashMod(k, bucket.localDepth) == bucket.suffix
        LemmaPow2Factor(bucket.localDepth, next.globalDepth);
        var m :| m >= 1 && Pow2(next.globalDepth) == m * Pow2(bucket.localDepth);
        var ak := AbsKey(k);
        var q := ak / Pow2(next.globalDepth);
        assert ak == q * (m * Pow2(bucket.localDepth)) + dirIdx;
        assert ak == dirIdx + (q * m) * Pow2(bucket.localDepth);
        LemmaModMultipleAdd(dirIdx, q * m, Pow2(bucket.localDepth));
        assert HashMod(k, bucket.localDepth) == bucket.suffix;

        var newBucket := HashBucket(bucket.localDepth, bucket.suffix, updatedEntries);
        var newBuckets := next.buckets[bIdx := newBucket];
        next := next.(buckets := newBuckets);

        assert Entry(k, v) in updatedEntries;
        var hitIdx :| 0 <= hitIdx < |updatedEntries| && updatedEntries[hitIdx] == Entry(k, v);
        LemmaLookupEntriesHit(updatedEntries, hitIdx);
        assert Lookup(next, k) == Some(v);
        inserted := true;
        return;
      }

      if bucket.localDepth == next.maxDepth {
        // Reached configured maxDepth with a full bucket (hash collision bound)
        inserted := false;
        return;
      }

      if bucket.localDepth == next.globalDepth {
        ghost var prevGd := next.globalDepth;
        ghost var prevDirIdx := dirIdx;
        next := DoubleDirectory(next);
        dirIdx := HashMod(k, next.globalDepth);
        LemmaNextBitSplit(AbsKey(k), prevGd);
        assert dirIdx == prevDirIdx || dirIdx == prevDirIdx + Pow2(prevGd);
        assert next.directory[dirIdx] == bIdx;
      }

      // Note: `dirIdx` still maps to the same bucket `bIdx` with `localDepth < next.globalDepth`
      assert next.buckets[next.directory[dirIdx]].localDepth == bucket.localDepth;
      next := SplitBucket(next, dirIdx);
    }
  }
}
