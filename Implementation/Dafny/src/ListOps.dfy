/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Lists as bags
 *
 * The multiset operations a list-encoded marking needs, and what they do to the bag the list
 * represents.
 *
 * `Thesis/docs/mCRL2.md` 4.1 measures the reason this file exists: storing a marking as a
 * `List` rather than a `Bag` runs the thesis's own benchmark in 9 seconds instead of 67.
 * `Implementation/docs/Plan.md` 5 turns that sevenfold speedup into the project's largest open
 * question, because a list is not a bag:
 *
 * > A list-encoded marking is a *representative* of a bag, and the translation must be
 * > invariant under which representative it holds.
 *
 * Everything here is about that word *representative*. `BagOfSeq` is the map from a list to
 * the bag it represents; `EraseFirst`, `ListDiff` and `SubMultiset` are the list operations
 * mCRL2 can do quickly; and each is shown to compute, on the represented bag, exactly the
 * operation of Definition 1 that the bag encoding uses. Two lists with the same `BagOfSeq` are
 * therefore indistinguishable to the translation, which is the content of the order half of
 * `Plan.md` 5.
 */
module ListOps {

  import opened Std.Wrappers
  import opened Util
  import opened Color
  import opened Bag

  /** The number of times `v` occurs in `l`. */
  function CountOf(l: seq<Value>, v: Value): nat
  {
    if |l| == 0 then 0
    else (if l[0] == v then 1 else 0) + CountOf(l[1..], v)
  }

  /** The bag a list represents: every element with multiplicity one, so that the coefficient
    * of an item is the number of times the list holds it. */
  function BagOfSeq(l: seq<Value>): Bag
  {
    Bag(SeqEntries(l))
  }

  function SeqEntries(l: seq<Value>): seq<(Value, nat)>
  {
    if |l| == 0 then [] else [(l[0], 1)] + SeqEntries(l[1..])
  }

  lemma CoeffBagOfSeq(l: seq<Value>, v: Value)
    ensures Coeff(BagOfSeq(l), v) == CountOf(l, v)
  {
    if |l| != 0 {
      CoeffBagOfSeq(l[1..], v);
      var es := SeqEntries(l);
      assert es[0] == (l[0], 1);
      assert es[1..] == SeqEntries(l[1..]);
    }
  }

  lemma CountOfCons(u: Value, us: seq<Value>, v: Value)
    ensures CountOf([u] + us, v) == (if u == v then 1 else 0) + CountOf(us, v)
  {
    assert ([u] + us)[0] == u;
    assert ([u] + us)[1..] == us;
  }

  lemma CountOfAppend(a: seq<Value>, b: seq<Value>, v: Value)
    ensures CountOf(a + b, v) == CountOf(a, v) + CountOf(b, v)
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      CountOfAppend(a[1..], b, v);
      assert (a + b)[0] == a[0];
      assert (a + b)[1..] == a[1..] + b;
    }
  }

  lemma MemIffCountOf(l: seq<Value>, v: Value)
    ensures v in l <==> 0 < CountOf(l, v)
  {
    if |l| != 0 {
      MemIffCountOf(l[1..], v);
      assert v in l <==> (l[0] == v || v in l[1..]);
    }
  }

  // ---------------------------------------------------------------------------------------
  // Removing
  // ---------------------------------------------------------------------------------------

  /** `l` with the first occurrence of `v` dropped, which is mCRL2's `rm`. */
  function EraseFirst(l: seq<Value>, v: Value): seq<Value>
  {
    if |l| == 0 then []
    else if l[0] == v then l[1..]
    else [l[0]] + EraseFirst(l[1..], v)
  }

  lemma MemOfMemEraseFirst(l: seq<Value>, x: Value, v: Value)
    requires v in EraseFirst(l, x)
    ensures v in l
  {
    if |l| != 0 && l[0] != x {
      if v != l[0] {
        MemOfMemEraseFirst(l[1..], x, v);
      }
    }
  }

  lemma CountOfEraseFirst(l: seq<Value>, x: Value, v: Value)
    ensures CountOf(EraseFirst(l, x), v) == Sub(CountOf(l, v), if x == v then 1 else 0)
  {
    if |l| != 0 {
      if l[0] == x {
      } else {
        CountOfEraseFirst(l[1..], x, v);
        CountOfCons(l[0], EraseFirst(l[1..], x), v);
      }
    }
  }

  /** Multiset difference: `a` with one occurrence of each element of `b` dropped. */
  function ListDiff(a: seq<Value>, b: seq<Value>): seq<Value>
    decreases |b|
  {
    if |b| == 0 then a else ListDiff(EraseFirst(a, b[0]), b[1..])
  }

  lemma MemOfMemListDiff(a: seq<Value>, b: seq<Value>, v: Value)
    requires v in ListDiff(a, b)
    ensures v in a
    decreases |b|
  {
    if |b| != 0 {
      MemOfMemListDiff(EraseFirst(a, b[0]), b[1..], v);
      MemOfMemEraseFirst(a, b[0], v);
    }
  }

  lemma CountOfListDiff(a: seq<Value>, b: seq<Value>, v: Value)
    ensures CountOf(ListDiff(a, b), v) == Sub(CountOf(a, v), CountOf(b, v))
    decreases |b|
  {
    if |b| != 0 {
      CountOfListDiff(EraseFirst(a, b[0]), b[1..], v);
      CountOfEraseFirst(a, b[0], v);
    }
  }

  // ---------------------------------------------------------------------------------------
  // Inclusion
  // ---------------------------------------------------------------------------------------

  /** Multiset inclusion: every element of `a` can be matched with a distinct element of
    * `b`. */
  predicate SubMultiset(a: seq<Value>, b: seq<Value>)
  {
    if |a| == 0 then true
    else a[0] in b && SubMultiset(a[1..], EraseFirst(b, a[0]))
  }

  /** **The list operations compute Definition 1's operations on the bag the list
    * represents.**
    *
    * This one is the inclusion of operation 5; `CountOfAppend` and `CountOfListDiff` are
    * operations 2 and 6. Together they are what makes a list a faithful representative, and so
    * what makes the list encoding a candidate refinement of the bag encoding at all. */
  lemma SubMultisetIff(a: seq<Value>, b: seq<Value>)
    ensures SubMultiset(a, b) <==> forall v :: CountOf(a, v) <= CountOf(b, v)
  {
    if SubMultiset(a, b) {
      SubMultisetSound(a, b);
    } else {
      SubMultisetComplete(a, b);
    }
  }

  /** The forward half: what `SubMultiset` decides is inclusion of the represented bags. */
  lemma SubMultisetSound(a: seq<Value>, b: seq<Value>)
    requires SubMultiset(a, b)
    ensures forall v :: CountOf(a, v) <= CountOf(b, v)
  {
    if |a| == 0 {
    } else {
      var x := a[0];
      SubMultisetSound(a[1..], EraseFirst(b, x));
      assert [x] + a[1..] == a;
      MemIffCountOf(b, x);
      forall v ensures CountOf(a, v) <= CountOf(b, v) {
        CountOfCons(x, a[1..], v);
        CountOfEraseFirst(b, x, v);
      }
    }
  }

  /** The backward half, stated as a contrapositive so that the recursion runs on
    * `!SubMultiset` -- which is the form `SubMultisetIff`'s `else` branch hands it. */
  lemma SubMultisetComplete(a: seq<Value>, b: seq<Value>)
    requires !SubMultiset(a, b)
    ensures exists v :: CountOf(a, v) > CountOf(b, v)
  {
    var x := a[0];
    assert [x] + a[1..] == a;
    MemIffCountOf(b, x);
    if x !in b {
      CountOfCons(x, a[1..], x);
    } else {
      SubMultisetComplete(a[1..], EraseFirst(b, x));
      var w :| CountOf(a[1..], w) > CountOf(EraseFirst(b, x), w);
      CountOfCons(x, a[1..], w);
      CountOfEraseFirst(b, x, w);
      assert CountOf(a, w) > CountOf(b, w);
    }
  }
}
