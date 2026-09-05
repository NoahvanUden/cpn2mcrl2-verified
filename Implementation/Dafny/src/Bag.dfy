/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Bags
 *
 * Definition 1 of the thesis, made finitely supported.
 *
 * Definition 1 models a bag over `S` as a total function `m : S -> N`, and `Proof/` transcribes
 * it that way. `Implementation/docs/Plan.md` 4.1 requires the implementation to depart from
 * that:
 *
 * > So the implementation's bags are finitely supported from the start. This is a further
 * > departure from Definition 1 as printed.
 *
 * The reason is stated in `Thesis/docs/LeanFormalization.md` 5.1: inclusion of one total
 * function into another is a statement about all of `S`, which is not decidable, so the
 * condition of a summand could never be a `Bool`-valued *term*. Here a bag is a sequence of
 * coefficient entries, and the function Definition 1 calls the bag is recovered by `Coeff`.
 *
 * Dafny draws the line between the two in the language itself, which Lean does not: `Subset`
 * and `BagEquiv` quantify over `Value`, an infinite type, so they are `ghost predicate`s and
 * cannot appear in compiled code at all, while `SubsetB` is an ordinary `predicate` and can.
 * In Lean the same distinction is a `Decidable` instance that has to be found; here it is a
 * type error to confuse them, which is one of the few places the SMT-backed language is
 * *stricter* than the tactic-backed one.
 *
 * Every statement about bags below is phrased through `Coeff`, never through the entry
 * sequence: two bags with the same coefficients are the same bag as far as Definition 1 is
 * concerned, and `BagEquiv` is that equality. The representation is deliberately not
 * normalized -- `Union` is concatenation -- so the translator never has to sort or
 * deduplicate anything.
 */
module Bag {

  import opened Std.Wrappers
  import opened Util
  import opened Color

  /** **Definition 1 (Bag)**, finitely supported: a sequence of `(item, coefficient)` entries.
    *
    * The sequence is not required to be duplicate-free; `Coeff` sums the entries for an item,
    * so `Bag([(v, 1), (v, 1)])` and `Bag([(v, 2)])` are the same bag. */
  datatype Bag = Bag(entries: seq<(Value, nat)>)

  /** Truncated subtraction, which is what `-` is on `N`. Dafny's `nat` is a subset type and
    * its `-` is ordinary integer subtraction, so the truncation has to be written. */
  function Sub(a: nat, b: nat): nat
  {
    if a >= b then a - b else 0
  }

  /** The coefficient of `v` in a sequence of entries. */
  function EntryCoeff(es: seq<(Value, nat)>, v: Value): nat
  {
    if |es| == 0 then 0
    else (if es[0].0 == v then es[0].1 else 0) + EntryCoeff(es[1..], v)
  }

  /** The coefficient of `v` in `m`: the number of appearances of `v`, as Definition 1 has it.
    *
    * This is the bag in the sense of Definition 1; `entries` is only a representation of it. */
  function Coeff(m: Bag, v: Value): nat
  {
    EntryCoeff(m.entries, v)
  }

  /** Two bags are equal as bags when they have the same coefficients. */
  ghost predicate BagEquiv(m1: Bag, m2: Bag)
  {
    forall v :: Coeff(m1, v) == Coeff(m2, v)
  }

  /** The empty bag, written `0_MS` in the thesis. */
  function EmptyBag(): Bag
  {
    Bag([])
  }

  /** The bag the thesis writes `{n`v}`: `v` with coefficient `n`, everything else with
    * coefficient `0`. */
  function Single(n: nat, v: Value): Bag
  {
    Bag([(v, n)])
  }

  /** Operation 2, the union of two bags: the coefficients are added. */
  function Union(m1: Bag, m2: Bag): Bag
  {
    Bag(m1.entries + m2.entries)
  }

  /** The items an entry sequence mentions, with repetition. */
  function EntryKeys(es: seq<(Value, nat)>): seq<Value>
  {
    if |es| == 0 then [] else [es[0].0] + EntryKeys(es[1..])
  }

  /** The items a bag mentions, without repetition. Every item outside this sequence has
    * coefficient `0`, which is `CoeffZeroOfNotKey`. */
  function Keys(m: Bag): seq<Value>
  {
    Dedup(EntryKeys(m.entries))
  }

  function DiffEntries(ks: seq<Value>, m1: Bag, m2: Bag): seq<(Value, nat)>
  {
    if |ks| == 0 then []
    else [(ks[0], Sub(Coeff(m1, ks[0]), Coeff(m2, ks[0])))] + DiffEntries(ks[1..], m1, m2)
  }

  /** Operation 6, the difference of two bags: the coefficients are subtracted and floored at
    * zero, which is truncated subtraction on `N`. */
  function Diff(m1: Bag, m2: Bag): Bag
  {
    Bag(DiffEntries(Keys(m1), m1, m2))
  }

  /** Operation 5, the inclusion of one bag in another: every coefficient of `m1` is at most
    * the matching one of `m2`. Ghost, because the quantifier ranges over all of `Value`. */
  ghost predicate Subset(m1: Bag, m2: Bag)
  {
    forall v :: Coeff(m1, v) <= Coeff(m2, v)
  }

  function KeysLe(ks: seq<Value>, m1: Bag, m2: Bag): bool
  {
    if |ks| == 0 then true
    else Coeff(m1, ks[0]) <= Coeff(m2, ks[0]) && KeysLe(ks[1..], m1, m2)
  }

  /** Bag inclusion as a decision procedure.
    *
    * Finite support is exactly what makes this possible: only the items `m1` mentions have to
    * be checked, because its coefficient is `0` everywhere else. `SubsetBIff` is the statement
    * that this decides `Subset`. */
  predicate SubsetB(m1: Bag, m2: Bag)
  {
    KeysLe(Keys(m1), m1, m2)
  }

  /** A bag is well-typed for the color `c` when every item it mentions is. */
  predicate BagOfColor(m: Bag, c: Color)
  {
    EntriesOfColor(m.entries, c)
  }

  predicate EntriesOfColor(es: seq<(Value, nat)>, c: Color)
  {
    |es| == 0 || (ValueOfColor(es[0].0, c) && EntriesOfColor(es[1..], c))
  }

  // ---------------------------------------------------------------------------------------
  // The coefficient of each operation
  // ---------------------------------------------------------------------------------------

  lemma CoeffEmpty(v: Value)
    ensures Coeff(EmptyBag(), v) == 0
  {
  }

  lemma CoeffSingle(n: nat, u: Value, v: Value)
    ensures Coeff(Single(n, u), v) == (if u == v then n else 0)
  {
    var es := Single(n, u).entries;
    assert es == [(u, n)];
    assert |es| == 1;
    assert es[0] == (u, n);
    assert es[1..] == [];
    assert EntryCoeff(es[1..], v) == 0;
    assert Coeff(Single(n, u), v) == EntryCoeff(es, v);
  }

  lemma EntryCoeffAppend(a: seq<(Value, nat)>, b: seq<(Value, nat)>, v: Value)
    ensures EntryCoeff(a + b, v) == EntryCoeff(a, v) + EntryCoeff(b, v)
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      EntryCoeffAppend(a[1..], b, v);
      assert (a + b)[1..] == a[1..] + b;
      assert (a + b)[0] == a[0];
    }
  }

  lemma CoeffUnion(m1: Bag, m2: Bag, v: Value)
    ensures Coeff(Union(m1, m2), v) == Coeff(m1, v) + Coeff(m2, v)
  {
    EntryCoeffAppend(m1.entries, m2.entries, v);
  }

  lemma MemEntryKeys(es: seq<(Value, nat)>, v: Value)
    ensures v in EntryKeys(es) <==> exists i :: 0 <= i < |es| && es[i].0 == v
  {
    if |es| != 0 {
      MemEntryKeys(es[1..], v);
      if exists i :: 0 <= i < |es| && es[i].0 == v {
        var i :| 0 <= i < |es| && es[i].0 == v;
        if i != 0 {
          assert es[1..][i - 1].0 == v;
        }
      }
      if exists i :: 0 <= i < |es[1..]| && es[1..][i].0 == v {
        var i :| 0 <= i < |es[1..]| && es[1..][i].0 == v;
        assert es[i + 1].0 == v;
      }
    }
  }

  lemma EntryCoeffZeroOfNotKey(es: seq<(Value, nat)>, v: Value)
    requires v !in EntryKeys(es)
    ensures EntryCoeff(es, v) == 0
  {
    if |es| != 0 {
      EntryCoeffZeroOfNotKey(es[1..], v);
    }
  }

  lemma CoeffZeroOfNotKey(m: Bag, v: Value)
    requires v !in Keys(m)
    ensures Coeff(m, v) == 0
  {
    MemDedup(v, EntryKeys(m.entries));
    EntryCoeffZeroOfNotKey(m.entries, v);
  }

  lemma MemKeysOfCoeff(m: Bag, v: Value)
    requires Coeff(m, v) > 0
    ensures v in Keys(m)
  {
    if v !in Keys(m) {
      CoeffZeroOfNotKey(m, v);
    }
  }

  lemma EntryCoeffDiffEntries(ks: seq<Value>, m1: Bag, m2: Bag, v: Value)
    requires NoDup(ks)
    ensures EntryCoeff(DiffEntries(ks, m1, m2), v)
            == (if v in ks then Sub(Coeff(m1, v), Coeff(m2, v)) else 0)
  {
    if |ks| != 0 {
      EntryCoeffDiffEntries(ks[1..], m1, m2, v);
      if ks[0] == v {
        assert v !in ks[1..];
      }
    }
  }

  lemma MemEntryKeysDiffEntries(ks: seq<Value>, m1: Bag, m2: Bag, v: Value)
    ensures v in EntryKeys(DiffEntries(ks, m1, m2)) <==> v in ks
  {
    if |ks| != 0 {
      MemEntryKeysDiffEntries(ks[1..], m1, m2, v);
    }
  }

  lemma CoeffDiff(m1: Bag, m2: Bag, v: Value)
    ensures Coeff(Diff(m1, m2), v) == Sub(Coeff(m1, v), Coeff(m2, v))
  {
    NoDupDedup(EntryKeys(m1.entries));
    EntryCoeffDiffEntries(Keys(m1), m1, m2, v);
    if v !in Keys(m1) {
      CoeffZeroOfNotKey(m1, v);
    }
  }

  /** A bag well-typed for `c` has coefficient zero at every value that is not of color `c`.
    *
    * This is what lets a bag over all of `Value` be compared with a bag over the values *of
    * one color*, which is how the T2 statements relate a marking to a place's own color. */
  lemma CoeffZeroOfNotOfColor(m: Bag, c: Color, v: Value)
    requires BagOfColor(m, c)
    requires !ValueOfColor(v, c)
    ensures Coeff(m, v) == 0
  {
    EntriesCoeffZeroOfNotOfColor(m.entries, c, v);
  }

  lemma EntriesCoeffZeroOfNotOfColor(es: seq<(Value, nat)>, c: Color, v: Value)
    requires EntriesOfColor(es, c)
    requires !ValueOfColor(v, c)
    ensures EntryCoeff(es, v) == 0
  {
    if |es| != 0 {
      EntriesCoeffZeroOfNotOfColor(es[1..], c, v);
    }
  }

  /* The operations preserve well-typedness. `src/Typing.dfy` is what needs these: with typing
     extrinsic there is no index to carry the color, so each case of `EvalWf` has to be given
     the corresponding closure property by hand. */

  lemma BagOfColorEmpty(c: Color)
    ensures BagOfColor(EmptyBag(), c)
  {
  }

  lemma BagOfColorSingle(k: nat, v: Value, c: Color)
    requires ValueOfColor(v, c)
    ensures BagOfColor(Single(k, v), c)
  {
    assert Single(k, v).entries[1..] == [];
  }

  lemma BagOfColorUnion(m1: Bag, m2: Bag, c: Color)
    requires BagOfColor(m1, c)
    requires BagOfColor(m2, c)
    ensures BagOfColor(Union(m1, m2), c)
  {
    EntriesOfColorAppend(m1.entries, m2.entries, c);
  }

  lemma MemEntryKeysOfColor(es: seq<(Value, nat)>, c: Color, v: Value)
    requires EntriesOfColor(es, c)
    requires v in EntryKeys(es)
    ensures ValueOfColor(v, c)
  {
    if es[0].0 != v {
      MemEntryKeysOfColor(es[1..], c, v);
    }
  }

  lemma DiffEntriesOfColor(ks: seq<Value>, m1: Bag, m2: Bag, c: Color)
    requires forall v :: v in ks ==> ValueOfColor(v, c)
    ensures EntriesOfColor(DiffEntries(ks, m1, m2), c)
  {
    if |ks| != 0 {
      DiffEntriesOfColor(ks[1..], m1, m2, c);
      var es := DiffEntries(ks, m1, m2);
      assert es[0].0 == ks[0];
      assert es[1..] == DiffEntries(ks[1..], m1, m2);
    }
  }

  /** A difference holds only tokens the left operand held, so it stays at its color. */
  lemma BagOfColorDiff(m1: Bag, m2: Bag, c: Color)
    requires BagOfColor(m1, c)
    ensures BagOfColor(Diff(m1, m2), c)
  {
    forall v | v in Keys(m1) ensures ValueOfColor(v, c) {
      MemDedup(v, EntryKeys(m1.entries));
      MemEntryKeysOfColor(m1.entries, c, v);
    }
    DiffEntriesOfColor(Keys(m1), m1, m2, c);
  }

  lemma EntriesOfColorAppend(a: seq<(Value, nat)>, b: seq<(Value, nat)>, c: Color)
    ensures EntriesOfColor(a + b, c) <==> (EntriesOfColor(a, c) && EntriesOfColor(b, c))
  {
    if |a| == 0 {
      assert a + b == b;
    } else {
      EntriesOfColorAppend(a[1..], b, c);
      assert (a + b)[1..] == a[1..] + b;
      assert (a + b)[0] == a[0];
    }
  }

  // ---------------------------------------------------------------------------------------
  // Inclusion
  // ---------------------------------------------------------------------------------------

  lemma KeysLeMem(ks: seq<Value>, m1: Bag, m2: Bag)
    ensures KeysLe(ks, m1, m2) <==> forall v :: v in ks ==> Coeff(m1, v) <= Coeff(m2, v)
  {
    if |ks| != 0 {
      KeysLeMem(ks[1..], m1, m2);
    }
  }

  /** `SubsetB` decides `Subset`. Only the items `m1` mentions need checking, since its
    * coefficient is zero everywhere else. */
  lemma SubsetBIff(m1: Bag, m2: Bag)
    ensures SubsetB(m1, m2) <==> Subset(m1, m2)
  {
    KeysLeMem(Keys(m1), m1, m2);
    if SubsetB(m1, m2) {
      forall v ensures Coeff(m1, v) <= Coeff(m2, v) {
        if v !in Keys(m1) {
          CoeffZeroOfNotKey(m1, v);
        }
      }
    }
  }

  // ---------------------------------------------------------------------------------------
  // `BagEquiv` is an equivalence, and the operations respect it
  // ---------------------------------------------------------------------------------------

  lemma EquivRefl(m: Bag)
    ensures BagEquiv(m, m)
  {
  }

  lemma EquivSymm(m1: Bag, m2: Bag)
    requires BagEquiv(m1, m2)
    ensures BagEquiv(m2, m1)
  {
  }

  lemma EquivTrans(m1: Bag, m2: Bag, m3: Bag)
    requires BagEquiv(m1, m2)
    requires BagEquiv(m2, m3)
    ensures BagEquiv(m1, m3)
  {
  }

  lemma EquivUnion(m1: Bag, m2: Bag, n1: Bag, n2: Bag)
    requires BagEquiv(m1, n1)
    requires BagEquiv(m2, n2)
    ensures BagEquiv(Union(m1, m2), Union(n1, n2))
  {
    forall v ensures Coeff(Union(m1, m2), v) == Coeff(Union(n1, n2), v) {
      CoeffUnion(m1, m2, v);
      CoeffUnion(n1, n2, v);
    }
  }

  lemma EquivDiff(m1: Bag, m2: Bag, n1: Bag, n2: Bag)
    requires BagEquiv(m1, n1)
    requires BagEquiv(m2, n2)
    ensures BagEquiv(Diff(m1, m2), Diff(n1, n2))
  {
    forall v ensures Coeff(Diff(m1, m2), v) == Coeff(Diff(n1, n2), v) {
      CoeffDiff(m1, m2, v);
      CoeffDiff(n1, n2, v);
    }
  }

  lemma EquivSubset(m1: Bag, m2: Bag, n1: Bag, n2: Bag)
    requires BagEquiv(m1, n1)
    requires BagEquiv(m2, n2)
    requires Subset(m1, m2)
    ensures Subset(n1, n2)
  {
  }
}
