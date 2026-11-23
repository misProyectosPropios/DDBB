// Core shared types, sorted-sequence invariants, and pure helper functions
// for the Storage & Indexing Internals module:
//   - B+ Tree (`BPlusTree.dfy`)
//   - Extendible Hashing (`ExtendibleHashing.dfy`)
//   - LSM-Tree (`LsmTree.dfy`)

module IndexingTypes {
  type Key = int
  type Value = int

  datatype Option<T> =
    | None
    | Some(value: T)

  datatype Entry = Entry(key: Key, val: Value)

  // Strict ascending order on a sequence of keys.
  predicate KeysStrictlySorted(keys: seq<Key>)
  {
    forall i, j :: 0 <= i < j < |keys| ==> keys[i] < keys[j]
  }

  // Strict ascending order on a sequence of `(key, val)` entries.
  predicate EntriesStrictlySorted(entries: seq<Entry>)
  {
    forall i, j :: 0 <= i < j < |entries| ==> entries[i].key < entries[j].key
  }

  // Optional lower/upper key bounds for B+ Tree subtrees:
  //   - `lower == Some(lo)` means every key `k` must satisfy `lo <= k`.
  //   - `upper == Some(hi)` means every key `k` must satisfy `k < hi`.
  predicate KeyWithinBounds(k: Key, lower: Option<Key>, upper: Option<Key>)
  {
    (lower.Some? ==> lower.value <= k) &&
    (upper.Some? ==> k < upper.value)
  }

  predicate EntriesWithinBounds(entries: seq<Entry>, lower: Option<Key>, upper: Option<Key>)
  {
    forall i :: 0 <= i < |entries| ==> KeyWithinBounds(entries[i].key, lower, upper)
  }

  // Linear lookup in a strictly sorted entry sequence.
  function LookupEntries(entries: seq<Entry>, k: Key): Option<Value>
    decreases |entries|
  {
    if |entries| == 0 then None
    else if entries[0].key == k then Some(entries[0].val)
    else LookupEntries(entries[1..], k)
  }

  lemma LemmaLookupEntriesSound(entries: seq<Entry>, k: Key)
    requires EntriesStrictlySorted(entries)
    ensures LookupEntries(entries, k).Some? ==>
      Entry(k, LookupEntries(entries, k).value) in entries
    ensures LookupEntries(entries, k).None? ==>
      forall i :: 0 <= i < |entries| ==> entries[i].key != k
    decreases |entries|
  {
    if |entries| == 0 {
    } else if entries[0].key == k {
      assert entries[0] == Entry(k, entries[0].val);
    } else {
      LemmaLookupEntriesSound(entries[1..], k);
      if LookupEntries(entries[1..], k).Some? {
        var v := LookupEntries(entries[1..], k).value;
        assert Entry(k, v) in entries[1..];
        assert Entry(k, v) in entries;
      } else {
        forall i | 0 <= i < |entries|
          ensures entries[i].key != k
        {
          if i > 0 {
            assert entries[i] == entries[1..][i - 1];
          }
        }
      }
    }
  }

  lemma LemmaLookupEntriesHit(entries: seq<Entry>, idx: nat)
    requires EntriesStrictlySorted(entries)
    requires idx < |entries|
    ensures LookupEntries(entries, entries[idx].key) == Some(entries[idx].val)
    decreases |entries|
  {
    if idx == 0 {
    } else {
      assert entries[0].key < entries[idx].key;
      assert entries[1..][idx - 1] == entries[idx];
      LemmaLookupEntriesHit(entries[1..], idx - 1);
    }
  }

  // Inserts or updates `(k, v)` in a strictly sorted `entries` sequence,
  // preserving `EntriesStrictlySorted` and `EntriesWithinBounds`.
  function UpsertSortedEntry(entries: seq<Entry>, k: Key, v: Value): seq<Entry>
    requires EntriesStrictlySorted(entries)
    ensures EntriesStrictlySorted(UpsertSortedEntry(entries, k, v))
    ensures |UpsertSortedEntry(entries, k, v)| == |entries| ||
            |UpsertSortedEntry(entries, k, v)| == |entries| + 1
    ensures Entry(k, v) in UpsertSortedEntry(entries, k, v)
    ensures forall i :: 0 <= i < |UpsertSortedEntry(entries, k, v)| ==>
      UpsertSortedEntry(entries, k, v)[i] == Entry(k, v) ||
      UpsertSortedEntry(entries, k, v)[i] in entries
    decreases |entries|
  {
    if |entries| == 0 then
      [Entry(k, v)]
    else if k < entries[0].key then
      [Entry(k, v)] + entries
    else if k == entries[0].key then
      [Entry(k, v)] + entries[1..]
    else
      [entries[0]] + UpsertSortedEntry(entries[1..], k, v)
  }

  lemma LemmaUpsertPreservesBounds(
    entries: seq<Entry>,
    k: Key,
    v: Value,
    lower: Option<Key>,
    upper: Option<Key>
  )
    requires EntriesStrictlySorted(entries)
    requires EntriesWithinBounds(entries, lower, upper)
    requires KeyWithinBounds(k, lower, upper)
    ensures EntriesWithinBounds(UpsertSortedEntry(entries, k, v), lower, upper)
  {
    var res := UpsertSortedEntry(entries, k, v);
    forall i | 0 <= i < |res|
      ensures KeyWithinBounds(res[i].key, lower, upper)
    {
      if res[i] == Entry(k, v) {
      } else {
        assert res[i] in entries;
        var j :| 0 <= j < |entries| && entries[j] == res[i];
        assert KeyWithinBounds(entries[j].key, lower, upper);
      }
    }
  }

  // Filters entries whose key lies in `[lo, hi]`, preserving sorted order.
  function FilterRangeEntries(entries: seq<Entry>, lo: Key, hi: Key): seq<Entry>
    requires EntriesStrictlySorted(entries)
    ensures EntriesStrictlySorted(FilterRangeEntries(entries, lo, hi))
    ensures forall i :: 0 <= i < |FilterRangeEntries(entries, lo, hi)| ==>
      lo <= FilterRangeEntries(entries, lo, hi)[i].key <= hi
    ensures forall i :: 0 <= i < |FilterRangeEntries(entries, lo, hi)| ==>
      FilterRangeEntries(entries, lo, hi)[i] in entries
    decreases |entries|
  {
    if |entries| == 0 then
      []
    else
      var rest := FilterRangeEntries(entries[1..], lo, hi);
      if lo <= entries[0].key <= hi then
        [entries[0]] + rest
      else
        rest
  }

  // Power of 2 helper for Extendible Hashing (`Pow2(d) == 2^d`).
  function Pow2(d: nat): nat
    ensures Pow2(d) >= 1
    decreases d
  {
    if d == 0 then 1 else 2 * Pow2(d - 1)
  }
}
