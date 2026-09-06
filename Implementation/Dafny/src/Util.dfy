/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Sequence utilities
 *
 * Duplicate removal, association lookup, and the map/filter/fold the rest of the translator
 * needs, written out over `seq` rather than taken from `Std.Collections`.
 *
 * The Lean counterpart, `Cpn2mCrl2/Util.lean`, gives one reason for writing these by hand:
 * keeping Mathlib out of the trust boundary. Here the reason is different and worth naming,
 * because it is the first place Dafny and Lean diverge. Dafny's `seq<T>` is a built-in with
 * SMT support, so `NoDup` and `Lookup` are not needed to *avoid* a library -- they are needed
 * because the definitions have to be the ones the proofs unfold. A recursive `NoDup` over
 * `s[1..]` and a quantified `forall i, j` are interchangeable as specifications and are not
 * interchangeable as proof obligations, and every induction below is over the recursive one.
 *
 * `Dedup` deliberately keeps the *last* occurrence of an item, which is what
 * `Cpn2mCrl2/Util.lean`'s `dedup` does. Nothing here depends on that; it is so that the two
 * translators emit the summation variables of a summand in the same order and their outputs
 * can be compared as text.
 */
module Util {

  import opened Std.Wrappers

  /** No item of `s` occurs twice. Recursive rather than quantified, so that a proof about
    * `[x] + s` can unfold one step. */
  predicate NoDup<T(==)>(s: seq<T>)
  {
    |s| == 0 || (s[0] !in s[1..] && NoDup(s[1..]))
  }

  /** `a` prepended to `l`, unless `l` already contains it. */
  function InsertNew<T(==)>(a: T, l: seq<T>): seq<T>
  {
    if a in l then l else [a] + l
  }

  /** `s` without repetitions, keeping the last occurrence of each item. */
  function Dedup<T(==)>(s: seq<T>): seq<T>
  {
    if |s| == 0 then [] else InsertNew(s[0], Dedup(s[1..]))
  }

  lemma MemInsertNew<T>(a: T, b: T, l: seq<T>)
    ensures a in InsertNew(b, l) <==> (a == b || a in l)
  {
  }

  lemma MemDedup<T>(a: T, s: seq<T>)
    ensures a in Dedup(s) <==> a in s
  {
    if |s| != 0 {
      MemDedup(a, s[1..]);
      MemInsertNew(a, s[0], Dedup(s[1..]));
      assert a in s <==> (a == s[0] || a in s[1..]);
    }
  }

  lemma NoDupInsertNew<T>(a: T, l: seq<T>)
    requires NoDup(l)
    ensures NoDup(InsertNew(a, l))
  {
    if a !in l {
      assert ([a] + l)[1..] == l;
    }
  }

  lemma NoDupDedup<T>(s: seq<T>)
    ensures NoDup(Dedup(s))
  {
    if |s| != 0 {
      NoDupDedup(s[1..]);
      NoDupInsertNew(s[0], Dedup(s[1..]));
    }
  }

  /** The value `k` is associated with, if any. The first entry wins. */
  function Lookup<K(==), V>(l: seq<(K, V)>, k: K): Option<V>
  {
    if |l| == 0 then None
    else if l[0].0 == k then Some(l[0].1)
    else Lookup(l[1..], k)
  }

  /** The first item of `s` satisfying `p`, if any. */
  function Find<T>(s: seq<T>, p: T -> bool): Option<T>
  {
    if |s| == 0 then None
    else if p(s[0]) then Some(s[0])
    else Find(s[1..], p)
  }

  lemma FindMem<T>(s: seq<T>, p: T -> bool)
    ensures Find(s, p).Some? ==> Find(s, p).value in s && p(Find(s, p).value)
  {
    if |s| != 0 && !p(s[0]) {
      FindMem(s[1..], p);
    }
  }

  function Map<A, B>(f: A -> B, s: seq<A>): seq<B>
  {
    if |s| == 0 then [] else [f(s[0])] + Map(f, s[1..])
  }

  lemma MemMap<A, B>(f: A -> B, s: seq<A>, a: A)
    requires a in s
    ensures f(a) in Map(f, s)
  {
    if s[0] != a {
      assert a in s[1..];
      MemMap(f, s[1..], a);
    }
  }

  lemma MemMapInv<A, B>(f: A -> B, s: seq<A>, b: B)
    requires b in Map(f, s)
    ensures exists a :: a in s && f(a) == b
  {
    if f(s[0]) != b {
      MemMapInv(f, s[1..], b);
      var a :| a in s[1..] && f(a) == b;
      assert a in s;
    }
  }

  function Filter<T>(s: seq<T>, p: T -> bool): seq<T>
  {
    if |s| == 0 then []
    else if p(s[0]) then [s[0]] + Filter(s[1..], p)
    else Filter(s[1..], p)
  }

  lemma MemFilter<T>(s: seq<T>, p: T -> bool, a: T)
    ensures a in Filter(s, p) <==> (a in s && p(a))
  {
    if |s| != 0 {
      MemFilter(s[1..], p, a);
    }
  }

  function FlatMap<A, B>(f: A -> seq<B>, s: seq<A>): seq<B>
  {
    if |s| == 0 then [] else f(s[0]) + FlatMap(f, s[1..])
  }

  lemma MemFlatMap<A, B>(f: A -> seq<B>, s: seq<A>, b: B)
    ensures b in FlatMap(f, s) <==> exists a :: a in s && b in f(a)
  {
    if |s| != 0 {
      MemFlatMap(f, s[1..], b);
      if exists a :: a in s && b in f(a) {
        var a :| a in s && b in f(a);
        if a != s[0] {
          assert a in s[1..];
        }
      }
    }
  }

  predicate All<T>(s: seq<T>, p: T -> bool)
  {
    |s| == 0 || (p(s[0]) && All(s[1..], p))
  }

  lemma AllMem<T>(s: seq<T>, p: T -> bool)
    ensures All(s, p) <==> forall a :: a in s ==> p(a)
  {
    if |s| != 0 {
      AllMem(s[1..], p);
    }
  }

  lemma AllAppend<T>(a: seq<T>, b: seq<T>, p: T -> bool)
    ensures All(a + b, p) <==> (All(a, p) && All(b, p))
  {
    AllMem(a, p);
    AllMem(b, p);
    AllMem(a + b, p);
    assert forall x :: x in a + b <==> (x in a || x in b);
  }

  /** `parts`, separated by `sep`. */
  function Join(sep: string, parts: seq<string>): string
  {
    if |parts| == 0 then ""
    else if |parts| == 1 then parts[0]
    else parts[0] + sep + Join(sep, parts[1..])
  }

  /** The decimal digits of a natural number. */
  function NatToString(n: nat): string
    decreases n
  {
    if n < 10 then ['0' + (n as char)]
    else NatToString(n / 10) + ['0' + ((n % 10) as char)]
  }

  /** An integer in decimal, with a leading `-` when negative. */
  function IntToString(i: int): string
  {
    if i < 0 then "-" + NatToString(-i) else NatToString(i)
  }

  /** `s` with the entries whose keys repeat an earlier one dropped, keeping the first. Used
    * to emit one sort declaration per color rather than one per mention. */
  function DedupBy<T, K(==)>(s: seq<T>, key: T -> K): seq<T>
  {
    DedupByFrom(s, key, [])
  }

  function DedupByFrom<T, K(==)>(s: seq<T>, key: T -> K, seen: seq<K>): seq<T>
  {
    if |s| == 0 then []
    else if key(s[0]) in seen then DedupByFrom(s[1..], key, seen)
    else [s[0]] + DedupByFrom(s[1..], key, seen + [key(s[0])])
  }

  /** Insertion sort by a string key, so that the importer can present the entries of a JSON
    * object in a canonical order. */
  function SortByKey<V>(l: seq<(string, V)>): seq<(string, V)>
  {
    if |l| == 0 then []
    else InsertByKey(l[0], SortByKey(l[1..]))
  }

  function InsertByKey<V>(x: (string, V), l: seq<(string, V)>): seq<(string, V)>
  {
    if |l| == 0 then [x]
    else if StringLe(x.0, l[0].0) then [x] + l
    else [l[0]] + InsertByKey(x, l[1..])
  }

  /** Lexicographic order on strings, by code point. */
  predicate StringLe(a: string, b: string)
  {
    if |a| == 0 then true
    else if |b| == 0 then false
    else if a[0] != b[0] then a[0] < b[0]
    else StringLe(a[1..], b[1..])
  }
}
