/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Colored Petri Nets
 *
 * Definitions 4 and 5 of the thesis, as data a program can hold, together with the validation
 * that turns that data into a CPN.
 *
 * `Proof/ColoredPetriNets.lean` makes `P` and `T` Lean *types*, which discharges the finiteness
 * of Definition 4 and the disjointness `P cap T = 0` by construction. A file cannot carry a
 * type, so here they are sequences of named declarations and both conditions become checks.
 * That is the shift `Implementation/docs/Plan.md` 3 predicts:
 *
 * > The Definition 5 side conditions stop being decorative.
 *
 * `Thesis/docs/LeanFormalization.md` 4.5 records that `finitePlaces`, `finiteTransitions`,
 * `finiteColors`, `finiteV`, `boolMem`, `colorMem` and `varTypeMem` are declared in `Proof/`
 * and used by no proof. Every one of them appears below as a conjunct of `Valid`.
 *
 * ## What `Valid` carries here that it does not carry in Lean
 *
 * `Cpn2mCrl2/Net.lean` types the three annotation slots intrinsically: `PlaceDecl.init` is an
 * `Expr (.bag color)`, `TransDecl.guard` an `Expr (.color .bool)`, and `ArcDecl.expr` an
 * `Expr (.bag color)`. Nothing has to check those, because no other term can be put there.
 * Without dependent types they are ordinary `Expr`s and the four `WellTyped` conjuncts at the
 * end of `Valid` are what stands in. They are decided once by the importer, like every other
 * conjunct, so no cost falls on the user; the cost is four more hypotheses to thread, and
 * `src/Typing.dfy` explains where that actually bites.
 *
 * One thing gets *simpler*. `ArcDecl.exprAt` in Lean is
 * `if h : a.color = c then h |> a.expr else .emptyBag c`, a transport of a dependently typed
 * term along an equality proof, and three lemmas exist only to push evaluation, free variables
 * and scoping through that transport. Here `ExprAt` is an ordinary conditional and the
 * transport does not exist.
 *
 * ## Names are one namespace
 *
 * Definition 4 requires `P cap T = 0`. The emitted mCRL2 puts place names and variable names in
 * one scope -- the place parameters of `proc` and the `sum` variables of a summand -- so
 * `NamesDisjoint` extends the requirement to `V`.
 *
 * > **Addition to the thesis.** Definition 4 requires only `P cap T = 0`. `NamesDisjoint` also requires the names of `V` to be distinct from those of `P` and `T`, because the emitted specification binds a place and a variable in the same scope.
 *
 * ## Main definitions
 *
 * * `Net` : Definition 5, as data.
 * * `Valid` : the T1 checks of `InputFormat.md` 4.3.
 * * `Pre`, `Post`, `VarOf` : `pre(t)`, `post(t)` and `Var(t)`.
 */
module Nets {

  import opened Std.Wrappers
  import opened Util
  import opened Colors
  import opened Bags
  import opened ListOps
  import opened Exprs

  /** A place, with its color and its initialization expression `I(p)`. */
  datatype PlaceDecl = PlaceDecl(pname: string, pcolor: Color, pinit: Expr)

  /** A transition, with its guard `G(t)`. */
  datatype TransDecl = TransDecl(tname: string, guard: Expr)

  /** An arc together with its expression `E(a)`.
    *
    * The same datatype serves both sides of `A subseteq (P x T) union (T x P)`; which side an
    * arc is on is recorded by the field of `Net` it appears in, exactly as
    * `Proof/ColoredPetriNets.lean` splits `inArc` from `outArc`. */
  datatype ArcDecl = ArcDecl(aplace: string, atrans: string, acolor: Color, aexpr: Expr)

  /** **Definition 5 (Colored Petri Net)**, as data.
    *
    * The tuple `(P, T, A, Sigma, V, C, E, G, I)`, component for component: `places` carries
    * `P`, `C` and `I`; `transitions` carries `T` and `G`; `inArcs` and `outArcs` carry the two
    * sides of `A` together with `E`; `colors` is `Sigma` and `vars` is `V` with `Type[.]`.
    *
    * `Var(t)` and `pre(t)`/`post(t)` are derived, not stored, as
    * `Implementation/docs/InputFormat.md` 1 says they must be. */
  datatype Net = Net(
    colors: seq<Color>,
    vars: Ctx,
    places: seq<PlaceDecl>,
    transitions: seq<TransDecl>,
    inArcs: seq<ArcDecl>,
    outArcs: seq<ArcDecl>)

  /** The expression of an arc read at the color `c`, or the empty bag if the arc is not at that
    * color.
    *
    * The fallback never happens for a valid net -- `InArcPlace` and `OutArcPlace` are exactly
    * the statement that it does not -- but having it lets the translation be a total function
    * from `Net` to `Lpe` that needs no proof to run, with the proof appearing where
    * `Implementation/docs/Plan.md` 2 puts it: in T2, not in the program. */
  function ExprAt(a: ArcDecl, c: Color): Expr
  {
    if a.acolor == c then a.aexpr else EEmptyBag(c)
  }

  // ---------------------------------------------------------------------------------------
  // Lookups
  // ---------------------------------------------------------------------------------------

  function PlaceNames(ps: seq<PlaceDecl>): seq<string>
  {
    if |ps| == 0 then [] else [ps[0].pname] + PlaceNames(ps[1..])
  }

  function TransNames(ts: seq<TransDecl>): seq<string>
  {
    if |ts| == 0 then [] else [ts[0].tname] + TransNames(ts[1..])
  }

  function VarNames(vs: Ctx): seq<string>
  {
    if |vs| == 0 then [] else [vs[0].0] + VarNames(vs[1..])
  }

  /** The `(place, transition)` pairs of a set of arcs, which is what `A` being a set means. */
  function ArcKeys(arcs: seq<ArcDecl>): seq<(string, string)>
  {
    if |arcs| == 0 then []
    else [(arcs[0].aplace, arcs[0].atrans)] + ArcKeys(arcs[1..])
  }

  function FindPlace(ps: seq<PlaceDecl>, p: string): Option<PlaceDecl>
  {
    if |ps| == 0 then None
    else if ps[0].pname == p then Some(ps[0])
    else FindPlace(ps[1..], p)
  }

  /** `C(p)`, if `p` is a place of the net. */
  function PlaceColor(n: Net, p: string): Option<Color>
  {
    match FindPlace(n.places, p)
    case Some(d) => Some(d.pcolor)
    case None => None
  }

  /** The arc `(p, t)`, if there is one. */
  function InArc(n: Net, p: string, t: string): Option<ArcDecl>
  {
    FindArc(n.inArcs, p, t)
  }

  /** The arc `(t, p)`, if there is one. */
  function OutArc(n: Net, t: string, p: string): Option<ArcDecl>
  {
    FindArc(n.outArcs, p, t)
  }

  function FindArc(arcs: seq<ArcDecl>, p: string, t: string): Option<ArcDecl>
  {
    if |arcs| == 0 then None
    else if arcs[0].aplace == p && arcs[0].atrans == t then Some(arcs[0])
    else FindArc(arcs[1..], p, t)
  }

  function ArcsOf(arcs: seq<ArcDecl>, t: string): seq<ArcDecl>
  {
    if |arcs| == 0 then []
    else if arcs[0].atrans == t then [arcs[0]] + ArcsOf(arcs[1..], t)
    else ArcsOf(arcs[1..], t)
  }

  /** `pre(t)`, as the arcs into `t` rather than as the places -- which is the same data, and
    * carries `E(p, t)` with it. */
  function Pre(n: Net, t: string): seq<ArcDecl>
  {
    ArcsOf(n.inArcs, t)
  }

  /** `post(t)`, as the arcs out of `t`. */
  function Post(n: Net, t: string): seq<ArcDecl>
  {
    ArcsOf(n.outArcs, t)
  }

  function ArcVars(arcs: seq<ArcDecl>): Ctx
  {
    if |arcs| == 0 then [] else FreeVars(arcs[0].aexpr) + ArcVars(arcs[1..])
  }

  /** `Var(t)`, the variables appearing in the guard of `t` and in the arc expressions of the
    * arcs connected to `t`.
    *
    * Derived, never stored. Duplicates are removed so that the emitted `sum` binds each
    * variable once. */
  function VarOf(n: Net, t: TransDecl): Ctx
  {
    Dedup(FreeVars(t.guard) + ArcVars(Pre(n, t.tname)) + ArcVars(Post(n, t.tname)))
  }

  // ---------------------------------------------------------------------------------------
  // Membership lemmas for the lookups
  // ---------------------------------------------------------------------------------------

  lemma MemPlaceNames(ps: seq<PlaceDecl>, d: PlaceDecl)
    requires d in ps
    ensures d.pname in PlaceNames(ps)
  {
    if ps[0] != d {
      MemPlaceNames(ps[1..], d);
    }
  }

  lemma MemPlaceNamesInv(ps: seq<PlaceDecl>, x: string)
    requires x in PlaceNames(ps)
    ensures exists d :: d in ps && d.pname == x
  {
    if ps[0].pname != x {
      MemPlaceNamesInv(ps[1..], x);
      var d :| d in ps[1..] && d.pname == x;
      assert d in ps;
    }
  }

  lemma MemTransNames(ts: seq<TransDecl>, t: TransDecl)
    requires t in ts
    ensures t.tname in TransNames(ts)
  {
    if ts[0] != t {
      MemTransNames(ts[1..], t);
    }
  }

  lemma MemVarNames(vs: Ctx, q: (string, ExprTy))
    requires q in vs
    ensures q.0 in VarNames(vs)
  {
    if vs[0] != q {
      MemVarNames(vs[1..], q);
    }
  }

  lemma MemArcKeys(arcs: seq<ArcDecl>, a: ArcDecl)
    requires a in arcs
    ensures (a.aplace, a.atrans) in ArcKeys(arcs)
  {
    if arcs[0] != a {
      MemArcKeys(arcs[1..], a);
    }
  }

  lemma FindPlaceSome(ps: seq<PlaceDecl>, p: string)
    ensures FindPlace(ps, p).Some? ==>
              FindPlace(ps, p).value in ps && FindPlace(ps, p).value.pname == p
  {
    if |ps| != 0 && ps[0].pname != p {
      FindPlaceSome(ps[1..], p);
    }
  }

  /** The head of a duplicate-free place sequence shares its name with nothing in the tail.
    *
    * The one step every lookup-by-name induction needs, and the only place `PlacesNoDup` is
    * ever taken apart. `src/Translate.dfy` uses it twice more. */
  lemma HeadNameFresh(ps: seq<PlaceDecl>, d: PlaceDecl)
    requires |ps| > 0
    requires NoDup(PlaceNames(ps))
    requires d in ps[1..]
    ensures ps[0].pname != d.pname
  {
    MemPlaceNames(ps[1..], d);
    assert PlaceNames(ps)[0] == ps[0].pname;
    assert PlaceNames(ps)[1..] == PlaceNames(ps[1..]);
  }

  /** With the place names distinct, looking a place up by its own name finds it. This is where
    * `PlacesNoDup` -- one of the side conditions `LeanFormalization.md` 4.5 records as inert in
    * `Proof/` -- starts doing work. */
  lemma FindPlaceOfMem(ps: seq<PlaceDecl>, d: PlaceDecl)
    requires NoDup(PlaceNames(ps))
    requires d in ps
    ensures FindPlace(ps, d.pname) == Some(d)
  {
    if ps[0] != d {
      assert d in ps[1..];
      HeadNameFresh(ps, d);
      FindPlaceOfMem(ps[1..], d);
    }
  }

  lemma FindArcSome(arcs: seq<ArcDecl>, p: string, t: string)
    ensures FindArc(arcs, p, t).Some? ==>
              && FindArc(arcs, p, t).value in arcs
              && FindArc(arcs, p, t).value.aplace == p
              && FindArc(arcs, p, t).value.atrans == t
  {
    if |arcs| != 0 && !(arcs[0].aplace == p && arcs[0].atrans == t) {
      FindArcSome(arcs[1..], p, t);
    }
  }

  lemma MemArcsOf(arcs: seq<ArcDecl>, t: string, a: ArcDecl)
    ensures a in ArcsOf(arcs, t) <==> (a in arcs && a.atrans == t)
  {
    if |arcs| != 0 {
      MemArcsOf(arcs[1..], t, a);
    }
  }

  lemma MemArcVars(arcs: seq<ArcDecl>, a: ArcDecl, q: (string, ExprTy))
    requires a in arcs
    requires q in FreeVars(a.aexpr)
    ensures q in ArcVars(arcs)
  {
    if arcs[0] != a {
      MemArcVars(arcs[1..], a, q);
    }
  }

  lemma MemVarOfGuard(n: Net, t: TransDecl, q: (string, ExprTy))
    requires q in FreeVars(t.guard)
    ensures q in VarOf(n, t)
  {
    MemDedup(q, FreeVars(t.guard) + ArcVars(Pre(n, t.tname)) + ArcVars(Post(n, t.tname)));
  }

  lemma MemVarOfPre(n: Net, t: TransDecl, a: ArcDecl, q: (string, ExprTy))
    requires a in Pre(n, t.tname)
    requires q in FreeVars(a.aexpr)
    ensures q in VarOf(n, t)
  {
    MemArcVars(Pre(n, t.tname), a, q);
    MemDedup(q, FreeVars(t.guard) + ArcVars(Pre(n, t.tname)) + ArcVars(Post(n, t.tname)));
  }

  lemma MemVarOfPost(n: Net, t: TransDecl, a: ArcDecl, q: (string, ExprTy))
    requires a in Post(n, t.tname)
    requires q in FreeVars(a.aexpr)
    ensures q in VarOf(n, t)
  {
    MemArcVars(Post(n, t.tname), a, q);
    MemDedup(q, FreeVars(t.guard) + ArcVars(Pre(n, t.tname)) + ArcVars(Post(n, t.tname)));
  }

  // ---------------------------------------------------------------------------------------
  // Validity
  //
  // The T1 checks of `Implementation/docs/InputFormat.md` 4.3, plus what `src/Print.dfy` needs
  // to emit legal mCRL2. Every conjunct is a compiled `predicate`, so the importer can decide
  // the whole thing at the boundary and hand it to the core as a hypothesis.
  //
  // One named predicate per conjunct, which is how `Cpn2mCrl2/Net.lean` spells it as a
  // `structure Valid : Prop` with one field each. The names are what `src/Import.dfy` reports
  // when a net is refused, so a rejection can say which condition failed.
  // ---------------------------------------------------------------------------------------

  /** The places have distinct names: `P` is a set. */
  predicate PlacesNoDup(n: Net) { NoDup(PlaceNames(n.places)) }

  /** The transitions have distinct names: `T` is a set. */
  predicate TransNoDup(n: Net) { NoDup(TransNames(n.transitions)) }

  /** The variables have distinct names: `V` is a set. */
  predicate VarsNoDup(n: Net) { NoDup(VarNames(n.vars)) }

  /** No name is used twice across `P`, `T` and `V`. The `P cap T = 0` of Definition 4, extended
    * to `V` because the emitted specification binds a place and a variable in one scope. */
  predicate NamesDisjoint(n: Net)
  {
    forall x :: x in PlaceNames(n.places) ==>
      x !in TransNames(n.transitions) && x !in VarNames(n.vars)
  }

  /** No transition shares a name with a variable. */
  predicate TransVarsDisjoint(n: Net)
  {
    forall x :: x in TransNames(n.transitions) ==> x !in VarNames(n.vars)
  }

  /** `Bool in Sigma`, as Definition 5 requires. */
  predicate BoolMem(n: Net) { CBool in n.colors }

  /** `C(p) in Sigma` for every place. */
  predicate ColorMem(n: Net) { forall d :: d in n.places ==> d.pcolor in n.colors }

  /** Every variable of `V` is typed by a color, not by a bag or a list. Definition 5's
    * `Type[v] in Sigma` presupposes it; `src/Expr.dfy` allows bag-sorted variables only so that
    * Definition 14 can build the place parameters. */
  predicate VarsAreColors(n: Net) { forall q :: q in n.vars ==> IsColorSort(q.1) }

  /** `Type[v] in Sigma` for every variable of `V`. */
  predicate VarTypeMem(n: Net) { forall q :: q in n.vars ==> q.1.c in n.colors }

  /** Every in-arc names a place of the net, at that place's color. */
  predicate InArcPlace(n: Net)
  {
    forall a :: a in n.inArcs ==> PlaceColor(n, a.aplace) == Some(a.acolor)
  }

  /** Every out-arc names a place of the net, at that place's color. */
  predicate OutArcPlace(n: Net)
  {
    forall a :: a in n.outArcs ==> PlaceColor(n, a.aplace) == Some(a.acolor)
  }

  /** Every in-arc names a transition of the net. */
  predicate InArcTrans(n: Net)
  {
    forall a :: a in n.inArcs ==> a.atrans in TransNames(n.transitions)
  }

  /** Every out-arc names a transition of the net. */
  predicate OutArcTrans(n: Net)
  {
    forall a :: a in n.outArcs ==> a.atrans in TransNames(n.transitions)
  }

  /** `A` is a set: at most one arc from a given place to a given transition. */
  predicate InArcsNoDup(n: Net) { NoDup(ArcKeys(n.inArcs)) }

  /** `A` is a set: at most one arc from a given transition to a given place. */
  predicate OutArcsNoDup(n: Net) { NoDup(ArcKeys(n.outArcs)) }

  /** `I(p)` is closed, so that `M0` is well-defined without a binding. */
  predicate InitClosed(n: Net) { forall d :: d in n.places ==> FreeVars(d.pinit) == [] }

  /** `Var(t) subseteq V` for the guard. */
  predicate GuardScoped(n: Net)
  {
    forall t :: t in n.transitions ==> ScopedIn(n.vars, t.guard)
  }

  /** `Var(t) subseteq V` for the in-arc expressions. */
  predicate InArcScoped(n: Net)
  {
    forall a :: a in n.inArcs ==> ScopedIn(n.vars, a.aexpr)
  }

  /** `Var(t) subseteq V` for the out-arc expressions. */
  predicate OutArcScoped(n: Net)
  {
    forall a :: a in n.outArcs ==> ScopedIn(n.vars, a.aexpr)
  }

  /** `Type[I(p)] = C(p)_MS`. Free in Lean, where `PlaceDecl.init` is an `Expr (.bag color)`. */
  predicate InitTyped(n: Net)
  {
    forall d :: d in n.places ==> WellTyped(d.pinit, BT(d.pcolor))
  }

  /** `Type[G(t)] = Bool`, check 4 of `InputFormat.md` 4.3. Free in Lean. */
  predicate GuardTyped(n: Net)
  {
    forall t :: t in n.transitions ==> WellTyped(t.guard, CT(CBool))
  }

  /** `Type[E(a)] = C(p)_MS` for an in-arc, the rest of check 5. Free in Lean. */
  predicate InArcTyped(n: Net)
  {
    forall a :: a in n.inArcs ==> WellTyped(a.aexpr, BT(a.acolor))
  }

  /** The same for an out-arc. */
  predicate OutArcTyped(n: Net)
  {
    forall a :: a in n.outArcs ==> WellTyped(a.aexpr, BT(a.acolor))
  }

  /** The T1 validation of `Implementation/docs/InputFormat.md` 4.3.
    *
    * Conjunct by conjunct against that list: `PlacesNoDup`, `TransNoDup` and `NamesDisjoint`
    * are check 1 together with `P cap T = 0` of Definition 4; `ColorMem` and `BoolMem` are
    * check 2 and Definition 5's `Bool in Sigma`; `VarTypeMem` is check 3; checks 4 to 6 are
    * `GuardTyped`, `InArcTyped`, `OutArcTyped`, `InitTyped`, `InArcPlace`, `OutArcPlace` and
    * `InitClosed`; and `GuardScoped`, `InArcScoped` and `OutArcScoped` are check 7. */
  predicate Valid(n: Net)
  {
    && PlacesNoDup(n) && TransNoDup(n) && VarsNoDup(n)
    && NamesDisjoint(n) && TransVarsDisjoint(n)
    && BoolMem(n) && ColorMem(n) && VarsAreColors(n) && VarTypeMem(n)
    && InArcPlace(n) && OutArcPlace(n) && InArcTrans(n) && OutArcTrans(n)
    && InArcsNoDup(n) && OutArcsNoDup(n)
    && InitClosed(n) && GuardScoped(n) && InArcScoped(n) && OutArcScoped(n)
    && InitTyped(n) && GuardTyped(n) && InArcTyped(n) && OutArcTyped(n)
  }

  // ---------------------------------------------------------------------------------------
  // Consequences of validity used by the translation
  // ---------------------------------------------------------------------------------------

  lemma PlaceColorOfMem(n: Net, d: PlaceDecl)
    requires Valid(n)
    requires d in n.places
    ensures PlaceColor(n, d.pname) == Some(d.pcolor)
  {
    FindPlaceOfMem(n.places, d);
  }

  lemma MemPlaceNamesOfPlaceColor(n: Net, x: string, c: Color)
    requires PlaceColor(n, x) == Some(c)
    ensures x in PlaceNames(n.places)
  {
    FindPlaceSome(n.places, x);
    var d := FindPlace(n.places, x).value;
    MemPlaceNames(n.places, d);
  }

  lemma MemInArcsOfMemPre(n: Net, t: string, a: ArcDecl)
    requires a in Pre(n, t)
    ensures a in n.inArcs && a.atrans == t
  {
    MemArcsOf(n.inArcs, t, a);
  }

  lemma MemOutArcsOfMemPost(n: Net, t: string, a: ArcDecl)
    requires a in Post(n, t)
    ensures a in n.outArcs && a.atrans == t
  {
    MemArcsOf(n.outArcs, t, a);
  }

  /** An in-arc of a valid net carries the color of its place, so reading it at that color is
    * reading it at its own. In Lean this is `ArcDecl.eval_exprAt`, which has to transport a
    * dependently typed term along the equality; here the equality makes `ExprAt` reduce. */
  lemma InArcColor(n: Net, d: PlaceDecl, t: string, a: ArcDecl)
    requires Valid(n)
    requires d in n.places
    requires InArc(n, d.pname, t) == Some(a)
    ensures a.acolor == d.pcolor && a in n.inArcs && ExprAt(a, d.pcolor) == a.aexpr
  {
    FindArcSome(n.inArcs, d.pname, t);
    PlaceColorOfMem(n, d);
  }

  lemma OutArcColor(n: Net, d: PlaceDecl, t: string, a: ArcDecl)
    requires Valid(n)
    requires d in n.places
    requires OutArc(n, t, d.pname) == Some(a)
    ensures a.acolor == d.pcolor && a in n.outArcs && ExprAt(a, d.pcolor) == a.aexpr
  {
    FindArcSome(n.outArcs, d.pname, t);
    PlaceColorOfMem(n, d);
  }

  /** Reading an arc expression at another color leaves its free variables where they were, so
    * scoping survives. The mismatched case is the empty bag, which has none. */
  lemma ScopedInExprAt(g: Ctx, a: ArcDecl, c: Color)
    requires ScopedIn(g, a.aexpr)
    ensures ScopedIn(g, ExprAt(a, c))
  {
  }

  lemma WellTypedExprAt(a: ArcDecl, c: Color)
    requires WellTyped(a.aexpr, BT(a.acolor))
    ensures WellTyped(ExprAt(a, c), BT(c))
  {
  }
}
