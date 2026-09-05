/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # The translation
 *
 * Definition 14: the LPE a CPN is translated into, built as *terms*.
 *
 * Definition 14 spells out
 *
 *     c_t(d, h_t) = (forall p in pre(t) : E(p,t) subseteq s_p) and G(t)
 *     g_t(d, h_t) = ((s_p1 \ E(p1,t)) union E(t,p1), ..., (s_pn \ E(pn,t)) union E(t,pn))
 *
 * and both are written out below, from Definition 14's own text and from nothing else. The
 * discipline `Proof/MCRL2.lean` sets is kept: the translation does not call `Enabled` or
 * `Fire`, so `src/Correct.dfy` is a claim that can fail rather than a restatement.
 *
 * Unlike in `Proof/`, it can now fail in a second way. There the two sides were transcriptions
 * of one formula and agreed by `rfl`. Here one side is a predicate and the other is the
 * *evaluation of a term*, so the identity holds only if the term was assembled correctly out of
 * the right operations -- which is precisely the content
 * `Thesis/docs/LeanFormalization.md` 5 says `rfl` does not carry.
 *
 * ## What is total and what is checked
 *
 * `ToLpe` is a total function needing no proof to run. Where Definition 14 relies on a side
 * condition -- that the arc `(p,t)` carries an expression of type `C(p)_MS` -- the translation
 * falls back on the empty bag rather than demanding the proof, using `ExprAt`. For a valid net
 * the fallback never fires, and `src/Correct.dfy` shows it. This keeps the program and the
 * proof separate, as `Implementation/docs/Plan.md` 3 wants.
 *
 * Every function here is compiled. Nothing in the translation is ghost, and nothing in it
 * mentions `Eval`.
 *
 * ## Main definitions
 *
 * * `CondTerm` : `c_t`.
 * * `NextTerm` : one component of `g_t`.
 * * `ToLpe` : Definition 14.
 */
module Translate {

  import opened Std.Wrappers
  import opened Util
  import opened Color
  import opened Bag
  import opened ListOps
  import opened Expr
  import opened Net
  import opened Semantics
  import opened Lpe

  /** One conjunct of `c_t`: `E(p,t) subseteq s_p`, for an arc of `pre(t)`.
    *
    * The place parameter `s_p` is the variable named after the place, at bag sort -- see
    * `ToEnv` in `src/Semantics.dfy` for why the two namespaces cannot collide. */
  function CondConjunct(a: ArcDecl): Expr
  {
    EBagSubset(a.aexpr, EVar(a.aplace, BT(a.acolor)))
  }

  function CondConjuncts(arcs: seq<ArcDecl>): seq<Expr>
  {
    if |arcs| == 0 then [] else [CondConjunct(arcs[0])] + CondConjuncts(arcs[1..])
  }

  lemma MemCondConjuncts(arcs: seq<ArcDecl>, e: Expr)
    ensures e in CondConjuncts(arcs) <==> exists a :: a in arcs && e == CondConjunct(a)
  {
    if |arcs| != 0 {
      MemCondConjuncts(arcs[1..], e);
      if exists a :: a in arcs && e == CondConjunct(a) {
        var a :| a in arcs && e == CondConjunct(a);
        if a != arcs[0] {
          assert a in arcs[1..];
        }
      }
      if exists a :: a in arcs[1..] && e == CondConjunct(a) {
        var a :| a in arcs[1..] && e == CondConjunct(a);
        assert a in arcs;
      }
    }
  }

  /** `c_t(d, h_t) = (forall p in pre(t) : E(p,t) subseteq s_p) and G(t)`.
    *
    * The bounded quantifier is unfolded here, at translation time, into a finite conjunction
    * over the arcs of `pre(t)`: obligation 3 of `Implementation/docs/Plan.md` 4. */
  function CondTerm(n: Net, t: TransDecl): Expr
  {
    AndAll(CondConjuncts(Pre(n, t.tname)) + [t.guard])
  }

  /** `E(p,t)` as a term of the place's own bag sort.
    *
    * `ExprAt` reads the arc expression at the place's color; the two agree for a valid net and
    * the empty bag stands in otherwise. Where there is no arc the empty bag is what Definition
    * 7's convention on non-existing arcs prescribes anyway. */
  function ConsumeTerm(n: Net, t: TransDecl, d: PlaceDecl): Expr
  {
    match InArc(n, d.pname, t.tname)
    case Some(a) => ExprAt(a, d.pcolor)
    case None => EEmptyBag(d.pcolor)
  }

  /** `E(t,p)` as a term of the place's own bag sort, read as `ConsumeTerm` is. */
  function ProduceTerm(n: Net, t: TransDecl, d: PlaceDecl): Expr
  {
    match OutArc(n, t.tname, d.pname)
    case Some(a) => ExprAt(a, d.pcolor)
    case None => EEmptyBag(d.pcolor)
  }

  /** `g_t` at the place `d`: `(s_p \ E(p,t)) union E(t,p)`. */
  function NextTerm(n: Net, t: TransDecl, d: PlaceDecl): Expr
  {
    EBagUnion(EBagDiff(EVar(d.pname, BT(d.pcolor)), ConsumeTerm(n, t, d)),
              ProduceTerm(n, t, d))
  }

  function NextEntries(n: Net, t: TransDecl, ps: seq<PlaceDecl>): seq<(string, BagTerm)>
  {
    if |ps| == 0 then []
    else [(ps[0].pname, BagTerm(ps[0].pcolor, NextTerm(n, t, ps[0])))]
         + NextEntries(n, t, ps[1..])
  }

  /** The summand of `t`. `H_t` is `Var(t)`, `a_t` is `t` itself carrying no parameters. */
  function SummandOf(n: Net, t: TransDecl): Summand
  {
    Summand(VarOf(n, t), CondTerm(n, t), t.tname, NextEntries(n, t, n.places))
  }

  function SummandsOf(n: Net, ts: seq<TransDecl>): seq<Summand>
  {
    if |ts| == 0 then [] else [SummandOf(n, ts[0])] + SummandsOf(n, ts[1..])
  }

  function PlaceParams(ps: seq<PlaceDecl>): seq<(string, Color)>
  {
    if |ps| == 0 then [] else [(ps[0].pname, ps[0].pcolor)] + PlaceParams(ps[1..])
  }

  function InitEntries(ps: seq<PlaceDecl>): seq<(string, BagTerm)>
  {
    if |ps| == 0 then []
    else [(ps[0].pname, BagTerm(ps[0].pcolor, ps[0].pinit))] + InitEntries(ps[1..])
  }

  /** **Definition 14 (Translation).**
    * The LPE built from a CPN: one summand per transition, one bag-sorted parameter per place,
    * and `d0 = (I(p1)<>, ..., I(pn)<>)` -- emitted as the closed initialization *terms*, which
    * denote those values without the translator ever evaluating anything. */
  function ToLpe(n: Net): Lpe
  {
    Lpe(n.colors,
        PlaceParams(n.places),
        TransNames(n.transitions),
        SummandsOf(n, n.transitions),
        InitEntries(n.places))
  }

  // ---------------------------------------------------------------------------------------
  // Reading the pieces back out
  // ---------------------------------------------------------------------------------------

  lemma MemSummandsOf(n: Net, ts: seq<TransDecl>, s: Summand)
    ensures s in SummandsOf(n, ts) <==> exists t :: t in ts && s == SummandOf(n, t)
  {
    if |ts| != 0 {
      MemSummandsOf(n, ts[1..], s);
      if exists t :: t in ts && s == SummandOf(n, t) {
        var t :| t in ts && s == SummandOf(n, t);
        if t != ts[0] {
          assert t in ts[1..];
        }
      }
      if exists t :: t in ts[1..] && s == SummandOf(n, t) {
        var t :| t in ts[1..] && s == SummandOf(n, t);
        assert t in ts;
      }
    }
  }

  /** With the place names distinct, the next-state entry for a place is the one built for that
    * place. This is where `PlacesNoDup` does its second piece of work. */
  lemma LookupNextEntries(n: Net, t: TransDecl, ps: seq<PlaceDecl>, d: PlaceDecl)
    requires NoDup(PlaceNames(ps))
    requires d in ps
    ensures Lookup(NextEntries(n, t, ps), d.pname)
            == Some(BagTerm(d.pcolor, NextTerm(n, t, d)))
  {
    if ps[0] != d {
      assert d in ps[1..];
      if ps[0].pname == d.pname {
        MemPlaceNames(ps[1..], d);
        assert PlaceNames(ps)[0] == ps[0].pname;
        assert PlaceNames(ps)[1..] == PlaceNames(ps[1..]);
        assert false;
      }
      var es := NextEntries(n, t, ps);
      assert es[0].0 == ps[0].pname;
      assert es[1..] == NextEntries(n, t, ps[1..]);
      LookupNextEntries(n, t, ps[1..], d);
    }
  }

  lemma LookupNextEntriesNone(n: Net, t: TransDecl, ps: seq<PlaceDecl>, p: string)
    requires p !in PlaceNames(ps)
    ensures Lookup(NextEntries(n, t, ps), p) == None
  {
    if |ps| != 0 {
      assert PlaceNames(ps)[0] == ps[0].pname;
      assert PlaceNames(ps)[1..] == PlaceNames(ps[1..]);
      var es := NextEntries(n, t, ps);
      assert es[0].0 == ps[0].pname;
      assert es[1..] == NextEntries(n, t, ps[1..]);
      LookupNextEntriesNone(n, t, ps[1..], p);
    }
  }

  lemma LookupInitEntries(ps: seq<PlaceDecl>, d: PlaceDecl)
    requires NoDup(PlaceNames(ps))
    requires d in ps
    ensures Lookup(InitEntries(ps), d.pname) == Some(BagTerm(d.pcolor, d.pinit))
  {
    if ps[0] != d {
      assert d in ps[1..];
      if ps[0].pname == d.pname {
        MemPlaceNames(ps[1..], d);
        assert PlaceNames(ps)[0] == ps[0].pname;
        assert PlaceNames(ps)[1..] == PlaceNames(ps[1..]);
        assert false;
      }
      var es := InitEntries(ps);
      assert es[0].0 == ps[0].pname;
      assert es[1..] == InitEntries(ps[1..]);
      LookupInitEntries(ps[1..], d);
    }
  }

  lemma LookupInitEntriesNone(ps: seq<PlaceDecl>, p: string)
    requires p !in PlaceNames(ps)
    ensures Lookup(InitEntries(ps), p) == None
  {
    if |ps| != 0 {
      assert PlaceNames(ps)[0] == ps[0].pname;
      assert PlaceNames(ps)[1..] == PlaceNames(ps[1..]);
      var es := InitEntries(ps);
      assert es[0].0 == ps[0].pname;
      assert es[1..] == InitEntries(ps[1..]);
      LookupInitEntriesNone(ps[1..], p);
    }
  }
}
