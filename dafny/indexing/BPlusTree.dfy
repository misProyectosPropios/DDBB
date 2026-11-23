// Formally Verified B+ Tree Index (`BPlusTreeIndex`).
//
// Models a classic B+ Tree where:
//   - All data entries `(key, val)` live exclusively in `Leaf` nodes at uniform
//     `height` (balanced tree invariant).
//   - `Internal(keys, children)` nodes store strictly sorted separator keys
//     routing searches: keys in `children[i]` are `< keys[i]` and `>= keys[i-1]`.
//   - Insertion performs textbook **Leaf Copy-Up Split** (separator key remains
//     in the right leaf and is copied up) and **Internal Push-Up Split**
//     (median separator key is pushed up to the parent), growing the root when
//     needed while formally preserving `ValidBPlusTree`.

include "Types.dfy"

module BPlusTreeIndex {
  import opened IndexingTypes

  datatype BPlusNode =
    | Leaf(entries: seq<Entry>)
    | Internal(keys: seq<Key>, children: seq<BPlusNode>)

  datatype BPlusTree = BPlusTree(
    maxKeys: nat,
    height: nat,
    root: BPlusNode
  )

  datatype InsertResult =
    | NoSplit(node: BPlusNode)
    | Split(left: BPlusNode, sepKey: Key, right: BPlusNode)

  // ---------------------------------------------------------------------------
  // Child Routing Bounds & Tree Invariants
  // ---------------------------------------------------------------------------

  function ChildLower(keys: seq<Key>, lower: Option<Key>, i: nat): Option<Key>
    requires i <= |keys|
  {
    if i == 0 then lower else Some(keys[i - 1])
  }

  function ChildUpper(keys: seq<Key>, upper: Option<Key>, i: nat): Option<Key>
    requires i <= |keys|
  {
    if i == |keys| then upper else Some(keys[i])
  }

  predicate ValidNode(
    node: BPlusNode,
    height: nat,
    maxKeys: nat,
    lower: Option<Key>,
    upper: Option<Key>
  )
    decreases height
  {
    maxKeys >= 2 &&
    if height == 0 then
      node.Leaf? &&
      |node.entries| <= maxKeys &&
      EntriesStrictlySorted(node.entries) &&
      EntriesWithinBounds(node.entries, lower, upper)
    else
      node.Internal? &&
      1 <= |node.keys| <= maxKeys &&
      |node.children| == |node.keys| + 1 &&
      KeysStrictlySorted(node.keys) &&
      (forall i :: 0 <= i < |node.keys| ==> KeyWithinBounds(node.keys[i], lower, upper)) &&
      (forall i :: 0 <= i < |node.children| ==>
                     ValidNode(
                       node.children[i],
                       height - 1,
                       maxKeys,
                       ChildLower(node.keys, lower, i),
                       ChildUpper(node.keys, upper, i)
                     ))
  }

  predicate ValidBPlusTree(tree: BPlusTree)
  {
    tree.maxKeys >= 2 &&
    ValidNode(tree.root, tree.height, tree.maxKeys, None, None)
  }

  function EmptyBPlusTree(maxKeys: nat): BPlusTree
    requires maxKeys >= 2
    ensures ValidBPlusTree(EmptyBPlusTree(maxKeys))
  {
    BPlusTree(maxKeys, 0, Leaf([]))
  }

  // ---------------------------------------------------------------------------
  // Flattened Leaf-Level Entry Sequence (Logical Leaf Chain)
  // ---------------------------------------------------------------------------

  function AllChildrenEntries(children: seq<BPlusNode>): seq<Entry>
    decreases children
  {
    if |children| == 0 then []
    else AllEntries(children[0]) + AllChildrenEntries(children[1..])
  }

  function AllEntries(node: BPlusNode): seq<Entry>
    decreases node
  {
    match node
    case Leaf(entries) => entries
    case Internal(_, children) => AllChildrenEntries(children)
  }

  lemma LemmaChildInAllChildrenEntries(children: seq<BPlusNode>, idx: nat, e: Entry)
    requires idx < |children|
    requires e in AllEntries(children[idx])
    ensures e in AllChildrenEntries(children)
    decreases children
  {
    if idx == 0 {
    } else {
      LemmaChildInAllChildrenEntries(children[1..], idx - 1, e);
    }
  }

  lemma LemmaAllChildrenEntriesBoundedAndSorted(
    keys: seq<Key>,
    children: seq<BPlusNode>,
    childHeight: nat,
    maxKeys: nat,
    lower: Option<Key>,
    upper: Option<Key>,
    startIdx: nat
  )
    requires maxKeys >= 2
    requires |children| == |keys| + 1
    requires KeysStrictlySorted(keys)
    requires forall i :: 0 <= i < |keys| ==> KeyWithinBounds(keys[i], lower, upper)
    requires forall i :: 0 <= i < |children| ==>
                           ValidNode(children[i], childHeight, maxKeys, ChildLower(keys, lower, i), ChildUpper(keys, upper, i))
    requires startIdx <= |children|
    ensures EntriesStrictlySorted(AllChildrenEntries(children[startIdx..]))
    ensures EntriesWithinBounds(
              AllChildrenEntries(children[startIdx..]),
              if startIdx < |children| then ChildLower(keys, lower, startIdx) else lower,
              upper
            )
    decreases childHeight + 1, 0, |children| - startIdx
  {
    if startIdx == |children| {
    } else {
      var head := children[startIdx];
      var headLo := ChildLower(keys, lower, startIdx);
      var headHi := ChildUpper(keys, upper, startIdx);
      LemmaAllEntriesSortedAndBounded(head, childHeight, maxKeys, headLo, headHi);
      LemmaAllChildrenEntriesBoundedAndSorted(keys, children, childHeight, maxKeys, lower, upper, startIdx + 1);

      var headEntries := AllEntries(head);
      var tailEntries := AllChildrenEntries(children[startIdx + 1..]);
      assert children[startIdx..] == [head] + children[startIdx + 1..];
      assert AllChildrenEntries(children[startIdx..]) == headEntries + tailEntries;

      if startIdx + 1 < |children| {
        var sep := keys[startIdx];
        assert headHi == Some(sep);
        assert ChildLower(keys, lower, startIdx + 1) == Some(sep);
        forall i, j | 0 <= i < |headEntries| && 0 <= j < |tailEntries|
          ensures headEntries[i].key < tailEntries[j].key
        {
          assert headEntries[i].key < sep;
          assert sep <= tailEntries[j].key;
        }
      }
    }
  }

  lemma LemmaAllEntriesSortedAndBounded(
    node: BPlusNode,
    height: nat,
    maxKeys: nat,
    lower: Option<Key>,
    upper: Option<Key>
  )
    requires ValidNode(node, height, maxKeys, lower, upper)
    ensures EntriesStrictlySorted(AllEntries(node))
    ensures EntriesWithinBounds(AllEntries(node), lower, upper)
    decreases height, 1, 0
  {
    if height == 0 {
    } else {
      LemmaAllChildrenEntriesBoundedAndSorted(node.keys, node.children, height - 1, maxKeys, lower, upper, 0);
      assert node.children[0..] == node.children;
    }
  }

  // ---------------------------------------------------------------------------
  // Routing, Search & Range Scan
  // ---------------------------------------------------------------------------

  // Finds the unique child slot `idx` (`0 <= idx <= |keys|`) for key `k`.
  function FindChildIndexLoop(keys: seq<Key>, k: Key, idx: nat): nat
    requires KeysStrictlySorted(keys)
    requires idx <= |keys|
    requires idx > 0 ==> keys[idx - 1] <= k
    ensures idx <= FindChildIndexLoop(keys, k, idx) <= |keys|
    ensures FindChildIndexLoop(keys, k, idx) > 0 ==> keys[FindChildIndexLoop(keys, k, idx) - 1] <= k
    ensures FindChildIndexLoop(keys, k, idx) < |keys| ==> k < keys[FindChildIndexLoop(keys, k, idx)]
    decreases |keys| - idx
  {
    if idx == |keys| || k < keys[idx] then
      idx
    else
      FindChildIndexLoop(keys, k, idx + 1)
  }

  function FindChildIndex(keys: seq<Key>, k: Key): nat
    requires KeysStrictlySorted(keys)
    ensures FindChildIndex(keys, k) <= |keys|
    ensures FindChildIndex(keys, k) > 0 ==> keys[FindChildIndex(keys, k) - 1] <= k
    ensures FindChildIndex(keys, k) < |keys| ==> k < keys[FindChildIndex(keys, k)]
  {
    FindChildIndexLoop(keys, k, 0)
  }

  function SearchNode(
    node: BPlusNode,
    height: nat,
    maxKeys: nat,
    lower: Option<Key>,
    upper: Option<Key>,
    k: Key
  ): Option<Value>
    requires ValidNode(node, height, maxKeys, lower, upper)
    ensures SearchNode(node, height, maxKeys, lower, upper, k).Some? ==>
              Entry(k, SearchNode(node, height, maxKeys, lower, upper, k).value) in AllEntries(node)
    decreases height
  {
    if height == 0 then
      var res := LookupEntries(node.entries, k);
      assert res.Some? ==> Entry(k, res.value) in node.entries by {
        LemmaLookupEntriesSound(node.entries, k);
      }
      res
    else
      var idx := FindChildIndex(node.keys, k);
      var res := SearchNode(
                   node.children[idx],
                   height - 1,
                   maxKeys,
                   ChildLower(node.keys, lower, idx),
                   ChildUpper(node.keys, upper, idx),
                   k
                 );
      assert res.Some? ==> Entry(k, res.value) in AllEntries(node) by {
        if res.Some? {
          LemmaChildInAllChildrenEntries(node.children, idx, Entry(k, res.value));
        }
      }
      res
  }

  function Search(tree: BPlusTree, k: Key): Option<Value>
    requires ValidBPlusTree(tree)
    ensures Search(tree, k).Some? ==>
              Entry(k, Search(tree, k).value) in AllEntries(tree.root)
  {
    SearchNode(tree.root, tree.height, tree.maxKeys, None, None, k)
  }

  // Range scan returning all entries in `[lo, hi]` in strictly ascending key order.
  method RangeScan(tree: BPlusTree, lo: Key, hi: Key) returns (res: seq<Entry>)
    requires ValidBPlusTree(tree)
    ensures EntriesStrictlySorted(res)
    ensures forall i :: 0 <= i < |res| ==> lo <= res[i].key <= hi
    ensures forall i :: 0 <= i < |res| ==> res[i] in AllEntries(tree.root)
  {
    LemmaAllEntriesSortedAndBounded(tree.root, tree.height, tree.maxKeys, None, None);
    res := FilterRangeEntries(AllEntries(tree.root), lo, hi);
  }

  // ---------------------------------------------------------------------------
  // Insertion with Leaf Copy-Up Split & Internal Push-Up Split
  // ---------------------------------------------------------------------------

  // Helper: validates an overfull internal node (`|newKeys| <= maxKeys + 1`)
  // and splits it at `mid` (pushing `newKeys[mid]` up) when `|newKeys| > maxKeys`.
  method RebuildOrSplitInternal(
    newKeys: seq<Key>,
    newChildren: seq<BPlusNode>,
    height: nat,
    maxKeys: nat,
    lower: Option<Key>,
    upper: Option<Key>
  ) returns (res: InsertResult)
    requires height > 0 && maxKeys >= 2
    requires 1 <= |newKeys| <= maxKeys + 1
    requires |newChildren| == |newKeys| + 1
    requires KeysStrictlySorted(newKeys)
    requires forall i :: 0 <= i < |newKeys| ==> KeyWithinBounds(newKeys[i], lower, upper)
    requires forall i :: 0 <= i < |newChildren| ==>
                           ValidNode(
                             newChildren[i],
                             height - 1,
                             maxKeys,
                             ChildLower(newKeys, lower, i),
                             ChildUpper(newKeys, upper, i)
                           )
    ensures res.NoSplit? ==> ValidNode(res.node, height, maxKeys, lower, upper)
    ensures res.Split? ==>
              KeyWithinBounds(res.sepKey, lower, upper) &&
              (lower.Some? ==> lower.value < res.sepKey) &&
              ValidNode(res.left, height, maxKeys, lower, Some(res.sepKey)) &&
              ValidNode(res.right, height, maxKeys, Some(res.sepKey), upper)
  {
    if |newKeys| <= maxKeys {
      res := NoSplit(Internal(newKeys, newChildren));
      return;
    }

    // Internal node overflow (`|newKeys| == maxKeys + 1 >= 3`): Push-Up Split!
    var mid := |newKeys| / 2;
    assert 1 <= mid < |newKeys|;
    var sepKey := newKeys[mid];
    assert newKeys[0] < sepKey;
    var leftKeys := newKeys[..mid];
    var rightKeys := newKeys[mid + 1..];
    var leftChildren := newChildren[..mid + 1];
    var rightChildren := newChildren[mid + 1..];

    var leftNode := Internal(leftKeys, leftChildren);
    var rightNode := Internal(rightKeys, rightChildren);

    forall i | 0 <= i < |leftChildren|
      ensures ValidNode(
                leftChildren[i],
                height - 1,
                maxKeys,
                ChildLower(leftKeys, lower, i),
                ChildUpper(leftKeys, Some(sepKey), i)
              )
    {
      assert leftChildren[i] == newChildren[i];
      assert ChildLower(leftKeys, lower, i) == ChildLower(newKeys, lower, i);
      assert ChildUpper(leftKeys, Some(sepKey), i) == ChildUpper(newKeys, upper, i);
    }

    forall j | 0 <= j < |rightChildren|
      ensures ValidNode(
                rightChildren[j],
                height - 1,
                maxKeys,
                ChildLower(rightKeys, Some(sepKey), j),
                ChildUpper(rightKeys, upper, j)
              )
    {
      var orig := mid + 1 + j;
      assert rightChildren[j] == newChildren[orig];
      assert ChildLower(rightKeys, Some(sepKey), j) == ChildLower(newKeys, lower, orig);
      assert ChildUpper(rightKeys, upper, j) == ChildUpper(newKeys, upper, orig);
    }

    res := Split(leftNode, sepKey, rightNode);
  }

  method InsertNode(
    node: BPlusNode,
    height: nat,
    maxKeys: nat,
    lower: Option<Key>,
    upper: Option<Key>,
    k: Key,
    v: Value
  ) returns (res: InsertResult)
    requires ValidNode(node, height, maxKeys, lower, upper)
    requires KeyWithinBounds(k, lower, upper)
    ensures res.NoSplit? ==> ValidNode(res.node, height, maxKeys, lower, upper)
    ensures res.Split? ==>
              KeyWithinBounds(res.sepKey, lower, upper) &&
              (lower.Some? ==> lower.value < res.sepKey) &&
              ValidNode(res.left, height, maxKeys, lower, Some(res.sepKey)) &&
              ValidNode(res.right, height, maxKeys, Some(res.sepKey), upper)
    decreases height
  {
    if height == 0 {
      var updated := UpsertSortedEntry(node.entries, k, v);
      LemmaUpsertPreservesBounds(node.entries, k, v, lower, upper);

      if |updated| <= maxKeys {
        res := NoSplit(Leaf(updated));
        return;
      }

      // Leaf overflow (`|updated| == maxKeys + 1 >= 3`): Copy-Up Split!
      var mid := |updated| / 2;
      assert 1 <= mid < |updated|;
      var leftEntries := updated[..mid];
      var rightEntries := updated[mid..];
      var sepKey := updated[mid].key;

      assert updated[0].key < sepKey;
      assert KeyWithinBounds(sepKey, lower, upper);
      assert EntriesWithinBounds(leftEntries, lower, Some(sepKey));
      assert EntriesWithinBounds(rightEntries, Some(sepKey), upper);
      res := Split(Leaf(leftEntries), sepKey, Leaf(rightEntries));
      return;
    }

    // Internal node: route to child `idx`
    var idx := FindChildIndex(node.keys, k);
    var childLo := ChildLower(node.keys, lower, idx);
    var childHi := ChildUpper(node.keys, upper, idx);
    assert KeyWithinBounds(k, childLo, childHi);

    var childRes := InsertNode(node.children[idx], height - 1, maxKeys, childLo, childHi, k, v);
    match childRes {
      case NoSplit(newChild) =>
        var newChildren := node.children[idx := newChild];
        res := NoSplit(Internal(node.keys, newChildren));
      case Split(leftChild, sepKey, rightChild) =>
        var newKeys := node.keys[..idx] + [sepKey] + node.keys[idx..];
        var newChildren := node.children[..idx] + [leftChild, rightChild] + node.children[idx + 1..];

        assert KeysStrictlySorted(newKeys);
        forall i | 0 <= i < |newChildren|
          ensures ValidNode(
                    newChildren[i],
                    height - 1,
                    maxKeys,
                    ChildLower(newKeys, lower, i),
                    ChildUpper(newKeys, upper, i)
                  )
        {
          if i < idx {
            assert newChildren[i] == node.children[i];
            assert ChildLower(newKeys, lower, i) == ChildLower(node.keys, lower, i);
            assert ChildUpper(newKeys, upper, i) == ChildUpper(node.keys, upper, i);
          } else if i == idx {
            assert newChildren[i] == leftChild;
            assert ChildLower(newKeys, lower, i) == childLo;
            assert ChildUpper(newKeys, upper, i) == Some(sepKey);
          } else if i == idx + 1 {
            assert newChildren[i] == rightChild;
            assert ChildLower(newKeys, lower, i) == Some(sepKey);
            assert ChildUpper(newKeys, upper, i) == childHi;
          } else {
            assert newChildren[i] == node.children[i - 1];
            assert ChildLower(newKeys, lower, i) == ChildLower(node.keys, lower, i - 1);
            assert ChildUpper(newKeys, upper, i) == ChildUpper(node.keys, upper, i - 1);
          }
        }

        res := RebuildOrSplitInternal(newKeys, newChildren, height, maxKeys, lower, upper);
    }
  }

  // Public B+ Tree insertion (handles root split by growing tree height by 1).
  method Insert(tree: BPlusTree, k: Key, v: Value) returns (nextTree: BPlusTree)
    requires ValidBPlusTree(tree)
    ensures ValidBPlusTree(nextTree)
    ensures nextTree.maxKeys == tree.maxKeys
    ensures nextTree.height == tree.height || nextTree.height == tree.height + 1
  {
    var res := InsertNode(tree.root, tree.height, tree.maxKeys, None, None, k, v);
    match res {
      case NoSplit(newRoot) =>
        nextTree := BPlusTree(tree.maxKeys, tree.height, newRoot);
      case Split(left, sepKey, right) =>
        var newRoot := Internal([sepKey], [left, right]);
        nextTree := BPlusTree(tree.maxKeys, tree.height + 1, newRoot);
    }
  }
}
