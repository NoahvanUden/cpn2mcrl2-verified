/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # The list backend, and the refinement it needs
 *
 * Milestone M6 of `Implementation/docs/Plan.md`, discharged a second time. `Thesis/docs/mCRL2.md`
 * 4.1 measures a sevenfold speedup for storing a marking as a `List` rather than a `Bag`, and
 * the reference generator of `Implementation/docs/Target.md` 3 takes it. `Plan.md` 5 says what
 * that costs:
 *
 * > That is a sevenfold speedup, and it is also a departure from the object Theorem 1 is about.
 * > Two refinements separate them.
 *
 * The two are **order** and **typing**. This file settles both.
 *
 * ## Order
 *
 * A list-encoded marking is a *representative* of a bag, and two orders of production give two
 * distinct list states with the same underlying bag. `Plan.md` 5:
 *
 * > Those states should be bisimilar, but they are not equal -- so the induced LTS has strictly
 * > more states than the reachability graph, and bisimilarity holds where isomorphism fails.
 * > That is a provable lemma. Nobody has proved it.
 *
 * `ListRel` is the relation "these two markings represent the same bags", and
 * `StepOfToLpeListStep` and `ToLpeListStepOfStep` are its two halves: a step of either encoding
 * is matched by a step of the other. Nothing anywhere asks two list states to be equal, which is
 * exactly why the order does not matter.
 *
 * ## Typing
 *
 * > A single tagged-union `token` sort shared by every place discards that, so nothing in the
 * > emitted specification prevents a place from holding a token of the wrong tag.
 *
 * Neither of `Plan.md` 5's two options is taken: this backend emits `List(C(p))`, one list sort
 * per place at that place's *own* color, so the invariant is the sort of the parameter and there
 * is nothing to preserve. `Thesis/docs/mCRL2.md` 4.1 attributes the speedup to `List` versus
 * `Bag` and says nothing about sharing a sort, so nothing is given up by not copying the
 * reference generator's tagged union.
 *
 * ## The one place the missing dependent types show
 *
 * `Cpn2mCrl2/ListEncoding.lean`'s `Expr.bagToList` matches only the five constructors that can
 * land at bag sort, and needs no other case, because the index rules the rest out. `BagToList`
 * here is a total function over the whole datatype and has a fallback branch that a well-sorted
 * bag term never reaches -- so it takes the place's color as an argument, to have something to
 * return, and `CoeffBagToList` carries `WellTyped(e, BT(c))` as a hypothesis where the Lean
 * carries it in the type.
 *
 * That trade is not all one way. The Lean pays for the same index elsewhere: because
 * `bagToList`'s matcher discriminates on the index it does *not* reduce definitionally, and
 * `Cpn2mCrl2/ListEncoding.lean` has to state five explicit equation lemmas beside it and warns
 * the next reader about the wrinkle. Here the function reduces and there are no equation lemmas.
 *
 * ## Main results
 *
 * * `ToLpeList` : the list-encoded LPE.
 * * `HoldsListCondTerm`, `CountOfListNextMarking` : the condition and the next state against the
 *   bag encoding's.
 * * `StepOfToLpeListStep`, `ToLpeListStepOfStep` : the refinement, as the two halves of a
 *   bisimulation.
 */
module ListEncoding {

  import opened Std.Wrappers
  import opened Util
  import opened Colors
  import opened Bags
  import opened ListOps
  import opened Exprs
  import opened Nets
  import opened Semantics
  import opened Lpes
  import opened Translate
  import opened Correct

  // ---------------------------------------------------------------------------------------
  // A bag term as a list term
  // ---------------------------------------------------------------------------------------

  /** `k` copies of `e`, as a list term. */
  function ReplicateT(c: Color, k: nat, e: Expr): Expr
  {
    if k == 0 then ENilList(c) else ESnoc(ReplicateT(c, k - 1, e), e)
  }

  lemma CountOfEvalReplicateT(c: Color, k: nat, e: Expr, env: Env, w: Value)
    ensures CountOf(AsSeq(Eval(ReplicateT(c, k, e), env)), w)
            == (if AsValue(Eval(e, env)) == w then k else 0)
  {
    if k != 0 {
      CountOfEvalReplicateT(c, k - 1, e, env, w);
      CountOfAppend(AsSeq(Eval(ReplicateT(c, k - 1, e), env)), [AsValue(Eval(e, env))], w);
    }
  }

  /** A bag term as the list term denoting one of its representatives.
    *
    * The `c` argument is what the Lean gets from the index: it is the color the result is a list
    * of, and it supplies the value of the fallback branch that a term of sort `BT(c)` never
    * reaches. Translating a bag-*sorted variable* to a list-sorted variable of the same name is
    * right only because the list encoding names its parameters the way the bag encoding does;
    * `CoeffBagToList` therefore assumes the term has no bag-sorted free variables, which
    * `VarsAreColors` gives for everything a CPN carries. */
  function BagToList(c: Color, e: Expr): Expr
  {
    match e
    case EVar(x, t) => (if t.BT? then EVar(x, LT(t.c)) else ENilList(c))
    case EEmptyBag(c0) => ENilList(c0)
    case ESingle(k, e0) => ReplicateT(c, k, e0)
    case EBagUnion(a, b) => EAppendList(BagToList(c, a), BagToList(c, b))
    case EBagDiff(a, b) => EDiffList(BagToList(c, a), BagToList(c, b))
    case _ => ENilList(c)
  }

  /** The list term is well-sorted whenever the bag term was. */
  lemma SortOfBagToList(c: Color, e: Expr)
    requires WellTyped(e, BT(c))
    ensures WellTyped(BagToList(c, e), LT(c))
  {
    match e
    case EVar(_, _) =>
    case EEmptyBag(_) =>
    case ESingle(k, e0) => SortOfReplicateT(c, k, e0);
    case EBagUnion(a, b) => SortOfBagToList(c, a); SortOfBagToList(c, b);
    case EBagDiff(a, b) => SortOfBagToList(c, a); SortOfBagToList(c, b);
    case _ =>
  }

  lemma SortOfReplicateT(c: Color, k: nat, e: Expr)
    requires WellTyped(e, CT(c))
    ensures WellTyped(ReplicateT(c, k, e), LT(c))
  {
    if k != 0 {
      SortOfReplicateT(c, k - 1, e);
    }
  }

  /** The free variables are the ones the bag term had. */
  lemma FreeVarsBagToList(c: Color, e: Expr, q: (string, ExprTy))
    requires WellTyped(e, BT(c))
    requires q in FreeVars(BagToList(c, e))
    ensures exists r :: r in FreeVars(e) && r.0 == q.0
  {
    match e
    case EVar(x, t) => assert (x, t) in FreeVars(e);
    case EEmptyBag(_) =>
    case ESingle(k, e0) => FreeVarsReplicateT(c, k, e0, q);
    case EBagUnion(a, b) =>
      if q in FreeVars(BagToList(c, a)) {
        FreeVarsBagToList(c, a, q);
      } else {
        FreeVarsBagToList(c, b, q);
      }
    case EBagDiff(a, b) =>
      if q in FreeVars(BagToList(c, a)) {
        FreeVarsBagToList(c, a, q);
      } else {
        FreeVarsBagToList(c, b, q);
      }
    case _ =>
  }

  lemma FreeVarsReplicateT(c: Color, k: nat, e: Expr, q: (string, ExprTy))
    requires q in FreeVars(ReplicateT(c, k, e))
    ensures exists r :: r in FreeVars(e) && r.0 == q.0
  {
    if k != 0 {
      if q in FreeVars(ReplicateT(c, k - 1, e)) {
        FreeVarsReplicateT(c, k - 1, e, q);
      }
    }
  }

  /** **The list term represents the bag term.**
    *
    * Under two environments that agree on the term's free variables -- which are all
    * color-sorted, so the list and bag environments agree on all of them -- the list the
    * translation builds has, for every token, exactly the coefficient the bag has. */
  lemma CoeffBagToList(c: Color, e: Expr, lenv: Env, benv: Env, v: Value)
    requires WellTyped(e, BT(c))
    requires forall q :: q in FreeVars(e) ==> IsColorSort(q.1)
    requires forall q :: q in FreeVars(e) ==> lenv(q.1, q.0) == benv(q.1, q.0)
    ensures CountOf(AsSeq(Eval(BagToList(c, e), lenv)), v) == Coeff(AsBag(Eval(e, benv)), v)
  {
    match e
    case EVar(x, t) =>
      // Vacuous: a term of sort `BT(c)` that is a variable has a bag-sorted variable free in
      // it, and the second precondition says every free variable is color-sorted. This is the
      // hypothesis `VarsAreColors` supplies at every call site.
      assert (x, t) in FreeVars(e);
      assert {:contradiction} IsColorSort(t);
    case EEmptyBag(_) =>
    case ESingle(k, e0) =>
      CountOfEvalReplicateT(c, k, e0, lenv, v);
      EvalCongr(e0, lenv, benv);
      CoeffSingle(k, AsValue(Eval(e0, benv)), v);
    case EBagUnion(a, b) =>
      CoeffBagToList(c, a, lenv, benv, v);
      CoeffBagToList(c, b, lenv, benv, v);
      CountOfAppend(AsSeq(Eval(BagToList(c, a), lenv)), AsSeq(Eval(BagToList(c, b), lenv)), v);
      CoeffUnion(AsBag(Eval(a, benv)), AsBag(Eval(b, benv)), v);
    case EBagDiff(a, b) =>
      CoeffBagToList(c, a, lenv, benv, v);
      CoeffBagToList(c, b, lenv, benv, v);
      CountOfListDiff(AsSeq(Eval(BagToList(c, a), lenv)),
                      AsSeq(Eval(BagToList(c, b), lenv)), v);
      CoeffDiff(AsBag(Eval(a, benv)), AsBag(Eval(b, benv)), v);
    case _ =>
  }

  // ---------------------------------------------------------------------------------------
  // The list-encoded LPE
  // ---------------------------------------------------------------------------------------

  /** The state of the list-encoded process: a list of tokens per place. */
  type ListMarking = string -> seq<Value>

  /** The environment the list-encoded terms are read in: the place parameters hold the lists,
    * the summation variables hold the binding. The counterpart of `ToEnv`. */
  ghost function ListToEnv(lm: ListMarking, b: Env): Env
  {
    (t: ExprTy, x: string) =>
      match t
      case CT(_) => b(t, x)
      case BT(_) => DBag(EmptyBag())
      case LT(_) => DList(lm(x))
  }

  /** Two markings represent the same bags.
    *
    * This is the relation the refinement is stated over, and it is deliberately *not* an
    * equality of lists: `Implementation/docs/Plan.md` 5's order problem is exactly that two
    * production orders give distinct lists here, and nothing below ever asks them to be
    * equal. */
  ghost predicate ListRel(lm: ListMarking, m: Marking)
  {
    forall p, v :: CountOf(lm(p), v) == Coeff(m(p), v)
  }

  /** `ListRel` at one place and one token. Stated as a lemma because the quantifier is over a
    * function application at an arrow-typed variable, and the trigger it gets does not fire on
    * its own inside the `forall` blocks below. */
  lemma ListRelAt(lm: ListMarking, m: Marking, p: string, v: Value)
    requires ListRel(lm, m)
    ensures CountOf(lm(p), v) == Coeff(m(p), v)
  {
  }

  /** A term of the state, at list sort. */
  datatype ListTerm = ListTerm(ltcolor: Color, ltterm: Expr)

  /** One summand of the list-encoded LPE. */
  datatype ListSummand = ListSummand(
    lbinder: Ctx, lcond: Expr, lact: string, lnext: seq<(string, ListTerm)>)

  /** Definition 13 with a list per place instead of a bag. */
  datatype ListLpe = ListLpe(
    lsorts: seq<Color>,
    lparams: seq<(string, Color)>,
    lacts: seq<string>,
    lsummands: seq<ListSummand>,
    linit: seq<(string, ListTerm)>)

  /** The marking a summand leads to. Unlike the bag encoding this is an equality and not an
    * equivalence: mCRL2's `List` is a free datatype, so the reached state is one particular list
    * -- which is precisely why the order problem needs an argument. */
  ghost function ListNextMarking(s: ListSummand, lm: ListMarking, b: Env): ListMarking
  {
    (p: string) =>
      match Lookup(s.lnext, p)
      case Some(lt) => AsSeq(Eval(lt.ltterm, ListToEnv(lm, b)))
      case None => lm(p)
  }

  /** `d0`, evaluated. */
  ghost function ListLpeInitMarking(l: ListLpe): ListMarking
  {
    (p: string) =>
      match Lookup(l.linit, p)
      case Some(lt) => AsSeq(Eval(lt.ltterm, JunkEnv()))
      case None => []
  }

  /** Definition 15 for the list encoding. */
  ghost predicate ListLpeStep(l: ListLpe, lm: ListMarking, a: string, lm': ListMarking)
  {
    exists s, b: Env ::
      && s in l.lsummands
      && s.lact == a
      && EnvWfOn(s.lbinder, b)
      && Holds(s.lcond, ListToEnv(lm, b))
      && forall p :: lm'(p) == ListNextMarking(s, lm, b)(p)
  }

  // ---------------------------------------------------------------------------------------
  // The translation
  // ---------------------------------------------------------------------------------------

  /** One conjunct of `c_t`, in the list encoding: `E(p,t)` is contained in the list at `p`. */
  function ListCondConjunct(a: ArcDecl): Expr
  {
    ESubList(BagToList(a.acolor, a.aexpr), EVar(a.aplace, LT(a.acolor)))
  }

  function ListCondConjuncts(arcs: seq<ArcDecl>): seq<Expr>
  {
    if |arcs| == 0 then [] else [ListCondConjunct(arcs[0])] + ListCondConjuncts(arcs[1..])
  }

  lemma MemListCondConjuncts(arcs: seq<ArcDecl>, e: Expr)
    ensures e in ListCondConjuncts(arcs) <==> exists a :: a in arcs && e == ListCondConjunct(a)
  {
    if |arcs| != 0 {
      MemListCondConjuncts(arcs[1..], e);
      if exists a :: a in arcs && e == ListCondConjunct(a) {
        var a :| a in arcs && e == ListCondConjunct(a);
        if a != arcs[0] {
          assert a in arcs[1..];
        }
      }
      if exists a :: a in arcs[1..] && e == ListCondConjunct(a) {
        var a :| a in arcs[1..] && e == ListCondConjunct(a);
        assert a in arcs;
      }
    }
  }

  /** `c_t`, in the list encoding. */
  function ListCondTerm(n: Net, t: TransDecl): Expr
  {
    AndAll(ListCondConjuncts(Pre(n, t.tname)) + [t.guard])
  }

  /** The list at `p` after `t` has taken its tokens out. Where there is no arc the list is
    * unchanged rather than differenced against the empty list, which is what keeps the emitted
    * text free of the `\ 0` the bag encoding writes. */
  function ListConsumed(n: Net, t: TransDecl, d: PlaceDecl): Expr
  {
    match InArc(n, d.pname, t.tname)
    case Some(a) =>
      EDiffList(EVar(d.pname, LT(d.pcolor)), BagToList(d.pcolor, ExprAt(a, d.pcolor)))
    case None => EVar(d.pname, LT(d.pcolor))
  }

  /** `g_t` at the place `d`, in the list encoding. */
  function ListNextTerm(n: Net, t: TransDecl, d: PlaceDecl): Expr
  {
    match OutArc(n, t.tname, d.pname)
    case Some(a) =>
      EAppendList(ListConsumed(n, t, d), BagToList(d.pcolor, ExprAt(a, d.pcolor)))
    case None => ListConsumed(n, t, d)
  }

  function ListNextEntries(n: Net, t: TransDecl, ps: seq<PlaceDecl>): seq<(string, ListTerm)>
  {
    if |ps| == 0 then []
    else [(ps[0].pname, ListTerm(ps[0].pcolor, ListNextTerm(n, t, ps[0])))]
         + ListNextEntries(n, t, ps[1..])
  }

  /** The summand of `t`, in the list encoding. */
  function ListSummandOf(n: Net, t: TransDecl): ListSummand
  {
    ListSummand(VarOf(n, t), ListCondTerm(n, t), t.tname, ListNextEntries(n, t, n.places))
  }

  function ListSummandsOf(n: Net, ts: seq<TransDecl>): seq<ListSummand>
  {
    if |ts| == 0 then [] else [ListSummandOf(n, ts[0])] + ListSummandsOf(n, ts[1..])
  }

  function ListInitEntries(ps: seq<PlaceDecl>): seq<(string, ListTerm)>
  {
    if |ps| == 0 then []
    else [(ps[0].pname, ListTerm(ps[0].pcolor, BagToList(ps[0].pcolor, ps[0].pinit)))]
         + ListInitEntries(ps[1..])
  }

  /** **The list-encoded LPE**: `Implementation/docs/Plan.md` 5's second backend, behind the same
    * translation as the first. */
  function ToLpeList(n: Net): ListLpe
  {
    ListLpe(n.colors,
            PlaceParams(n.places),
            TransNames(n.transitions),
            ListSummandsOf(n, n.transitions),
            ListInitEntries(n.places))
  }

  lemma MemListSummandsOf(n: Net, ts: seq<TransDecl>, s: ListSummand)
    ensures s in ListSummandsOf(n, ts) <==> exists t :: t in ts && s == ListSummandOf(n, t)
  {
    if |ts| != 0 {
      MemListSummandsOf(n, ts[1..], s);
      if exists t :: t in ts && s == ListSummandOf(n, t) {
        var t :| t in ts && s == ListSummandOf(n, t);
        if t != ts[0] {
          assert t in ts[1..];
        }
      }
      if exists t :: t in ts[1..] && s == ListSummandOf(n, t) {
        var t :| t in ts[1..] && s == ListSummandOf(n, t);
        assert t in ts;
      }
    }
  }

  lemma LookupListNextEntries(n: Net, t: TransDecl, ps: seq<PlaceDecl>, d: PlaceDecl)
    requires NoDup(PlaceNames(ps))
    requires d in ps
    ensures Lookup(ListNextEntries(n, t, ps), d.pname)
            == Some(ListTerm(d.pcolor, ListNextTerm(n, t, d)))
  {
    if ps[0] != d {
      assert d in ps[1..];
      HeadNameFresh(ps, d);
      var es := ListNextEntries(n, t, ps);
      assert es[0].0 == ps[0].pname;
      assert es[1..] == ListNextEntries(n, t, ps[1..]);
      LookupListNextEntries(n, t, ps[1..], d);
    }
  }

  lemma LookupListNextEntriesNone(n: Net, t: TransDecl, ps: seq<PlaceDecl>, p: string)
    requires p !in PlaceNames(ps)
    ensures Lookup(ListNextEntries(n, t, ps), p) == None
  {
    if |ps| != 0 {
      assert PlaceNames(ps)[0] == ps[0].pname;
      assert PlaceNames(ps)[1..] == PlaceNames(ps[1..]);
      var es := ListNextEntries(n, t, ps);
      assert es[0].0 == ps[0].pname;
      assert es[1..] == ListNextEntries(n, t, ps[1..]);
      LookupListNextEntriesNone(n, t, ps[1..], p);
    }
  }

  lemma LookupListInitEntries(ps: seq<PlaceDecl>, d: PlaceDecl)
    requires NoDup(PlaceNames(ps))
    requires d in ps
    ensures Lookup(ListInitEntries(ps), d.pname)
            == Some(ListTerm(d.pcolor, BagToList(d.pcolor, d.pinit)))
  {
    if ps[0] != d {
      assert d in ps[1..];
      HeadNameFresh(ps, d);
      var es := ListInitEntries(ps);
      assert es[0].0 == ps[0].pname;
      assert es[1..] == ListInitEntries(ps[1..]);
      LookupListInitEntries(ps[1..], d);
    }
  }

  lemma LookupListInitEntriesNone(ps: seq<PlaceDecl>, p: string)
    requires p !in PlaceNames(ps)
    ensures Lookup(ListInitEntries(ps), p) == None
  {
    if |ps| != 0 {
      assert PlaceNames(ps)[0] == ps[0].pname;
      assert PlaceNames(ps)[1..] == PlaceNames(ps[1..]);
      var es := ListInitEntries(ps);
      assert es[0].0 == ps[0].pname;
      assert es[1..] == ListInitEntries(ps[1..]);
      LookupListInitEntriesNone(ps[1..], p);
    }
  }

  // ---------------------------------------------------------------------------------------
  // The refinement
  //
  // Everything below compares the list encoding with the bag encoding of `src/Translate.dfy`,
  // which `src/Correct.dfy` has already tied to Definitions 6 and 7. Composing the two is what
  // makes the list encoding as justified as the bag one.
  // ---------------------------------------------------------------------------------------

  lemma IsColorOfScoped(n: Net, e: Expr)
    requires Valid(n)
    requires ScopedIn(n.vars, e)
    ensures forall q :: q in FreeVars(e) ==> IsColorSort(q.1)
  {
  }

  lemma AgreeListToEnv(g: Ctx, lm: ListMarking, b: Env)
    requires forall q :: q in g ==> IsColorSort(q.1)
    ensures forall q :: q in g ==> ListToEnv(lm, b)(q.1, q.0) == b(q.1, q.0)
  {
  }

  /** An expression of the net is evaluated the same in the list environment and in the binding
    * alone -- obligation 4 of `Implementation/docs/Plan.md` 4 once more, now separating the list
    * parameters from the summation variables. */
  lemma EvalToEnvList(n: Net, e: Expr, lm: ListMarking, b: Env)
    requires Valid(n)
    requires ScopedIn(n.vars, e)
    ensures Eval(e, ListToEnv(lm, b)) == Eval(e, b)
  {
    IsColorOfScoped(n, e);
    AgreeListToEnv(FreeVars(e), lm, b);
    EvalCongr(e, ListToEnv(lm, b), b);
  }

  /** The list an arc's expression translates to represents the bag it evaluates to. */
  lemma CountOfBagToListArc(n: Net, a: ArcDecl, c: Color, lm: ListMarking, b: Env, v: Value)
    requires Valid(n)
    requires a.acolor == c
    requires ScopedIn(n.vars, a.aexpr)
    requires WellTyped(a.aexpr, BT(a.acolor))
    ensures CountOf(AsSeq(Eval(BagToList(c, ExprAt(a, c)), ListToEnv(lm, b))), v)
            == Coeff(AsBag(Eval(a.aexpr, b)), v)
  {
    IsColorOfScoped(n, a.aexpr);
    AgreeListToEnv(FreeVars(a.aexpr), lm, b);
    CoeffBagToList(c, a.aexpr, ListToEnv(lm, b), b, v);
  }

  // -------------------------------------------------------------------- `c_t`

  lemma HoldsListCondConjunct(n: Net, a: ArcDecl, lm: ListMarking, m: Marking, b: Env)
    requires Valid(n)
    requires a in n.inArcs
    requires ListRel(lm, m)
    ensures Holds(ListCondConjunct(a), ListToEnv(lm, b))
            <==> Subset(AsBag(Eval(a.aexpr, b)), m(a.aplace))
  {
    var lenv := ListToEnv(lm, b);
    var la := AsSeq(Eval(BagToList(a.acolor, a.aexpr), lenv));
    assert Eval(EVar(a.aplace, LT(a.acolor)), lenv) == DList(lm(a.aplace));
    assert Eval(ListCondConjunct(a), lenv) == DVal(VBool(SubMultiset(la, lm(a.aplace))));
    forall v ensures CountOf(la, v) == Coeff(AsBag(Eval(a.aexpr, b)), v) {
      CountOfBagToListArc(n, a, a.acolor, lm, b, v);
    }
    forall v ensures CountOf(lm(a.aplace), v) == Coeff(m(a.aplace), v) {
      ListRelAt(lm, m, a.aplace, v);
    }
    SubMultisetOfCounts(la, lm(a.aplace), AsBag(Eval(a.aexpr, b)), m(a.aplace));
  }

  /** Multiset inclusion of two lists is bag inclusion of the two bags they represent.
    *
    * Split out as its own lemma rather than inlined: with the two counting hypotheses as
    * preconditions the solver has only them to instantiate, where in the caller's context the
    * same step is one quantified biconditional among many and does not fire. */
  lemma SubMultisetOfCounts(la: seq<Value>, lb: seq<Value>, ba: Bag, bb: Bag)
    requires forall v :: CountOf(la, v) == Coeff(ba, v)
    requires forall v :: CountOf(lb, v) == Coeff(bb, v)
    ensures SubMultiset(la, lb) <==> Subset(ba, bb)
  {
    if SubMultiset(la, lb) {
      SubMultisetSound(la, lb);
      forall v ensures Coeff(ba, v) <= Coeff(bb, v) {
      }
    } else {
      SubMultisetComplete(la, lb);
      var v :| CountOf(la, v) > CountOf(lb, v);
      assert Coeff(ba, v) > Coeff(bb, v);
    }
  }

  /** **The condition of the list encoding is the condition of the bag encoding.** */
  lemma HoldsListCondTerm(n: Net, t: TransDecl, lm: ListMarking, m: Marking, b: Env)
    requires Valid(n)
    requires t in n.transitions
    requires ListRel(lm, m)
    ensures Holds(ListCondTerm(n, t), ListToEnv(lm, b)) <==> Enabled(n, m, t, b)
  {
    var arcs := Pre(n, t.tname);
    var es := ListCondConjuncts(arcs) + [t.guard];
    HoldsAndAll(es, ListToEnv(lm, b));
    EvalToEnvList(n, t.guard, lm, b);
    assert t.guard in es;

    forall a | a in arcs
      ensures ListCondConjunct(a) in es
      ensures Holds(ListCondConjunct(a), ListToEnv(lm, b))
              <==> Subset(AsBag(Eval(a.aexpr, b)), m(a.aplace))
    {
      MemListCondConjuncts(arcs, ListCondConjunct(a));
      MemInArcsOfMemPre(n, t.tname, a);
      HoldsListCondConjunct(n, a, lm, m, b);
    }

    if Enabled(n, m, t, b) {
      forall e | e in es ensures Holds(e, ListToEnv(lm, b)) {
        if e != t.guard {
          MemListCondConjuncts(arcs, e);
          var a :| a in arcs && e == ListCondConjunct(a);
        }
      }
    }
  }

  // -------------------------------------------------------------------- `g_t`

  lemma CountOfListConsumed(n: Net, t: TransDecl, d: PlaceDecl, lm: ListMarking, m: Marking,
                            b: Env, v: Value)
    requires Valid(n)
    requires d in n.places
    requires ListRel(lm, m)
    ensures CountOf(AsSeq(Eval(ListConsumed(n, t, d), ListToEnv(lm, b))), v)
            == Sub(Coeff(m(d.pname), v), Coeff(Consume(n, t.tname, b, d.pname), v))
  {
    var lenv := ListToEnv(lm, b);
    match InArc(n, d.pname, t.tname)
    case None =>
    case Some(a) =>
      InArcColor(n, d, t.tname, a);
      CountOfBagToListArc(n, a, d.pcolor, lm, b, v);
      CountOfListDiff(lm(d.pname),
                      AsSeq(Eval(BagToList(d.pcolor, ExprAt(a, d.pcolor)), lenv)), v);
  }

  lemma CountOfListNextTerm(n: Net, t: TransDecl, d: PlaceDecl, lm: ListMarking, m: Marking,
                            b: Env, v: Value)
    requires Valid(n)
    requires d in n.places
    requires ListRel(lm, m)
    ensures CountOf(AsSeq(Eval(ListNextTerm(n, t, d), ListToEnv(lm, b))), v)
            == Coeff(Fire(n, m, t, b)(d.pname), v)
  {
    var lenv := ListToEnv(lm, b);
    CoeffUnion(Diff(m(d.pname), Consume(n, t.tname, b, d.pname)),
               Produce(n, t.tname, b, d.pname), v);
    CoeffDiff(m(d.pname), Consume(n, t.tname, b, d.pname), v);
    CountOfListConsumed(n, t, d, lm, m, b, v);
    match OutArc(n, t.tname, d.pname)
    case None =>
    case Some(a) =>
      OutArcColor(n, d, t.tname, a);
      CountOfBagToListArc(n, a, d.pcolor, lm, b, v);
      CountOfAppend(AsSeq(Eval(ListConsumed(n, t, d), lenv)),
                    AsSeq(Eval(BagToList(d.pcolor, ExprAt(a, d.pcolor)), lenv)), v);
  }

  /** **The next state of the list encoding represents the next state of the bag encoding.** */
  lemma CountOfListNextMarking(n: Net, t: TransDecl, lm: ListMarking, m: Marking, b: Env,
                               p: string, v: Value)
    requires Valid(n)
    requires ListRel(lm, m)
    ensures CountOf(ListNextMarking(ListSummandOf(n, t), lm, b)(p), v)
            == Coeff(Fire(n, m, t, b)(p), v)
  {
    if p in PlaceNames(n.places) {
      MemPlaceNamesInv(n.places, p);
      var d :| d in n.places && d.pname == p;
      LookupListNextEntries(n, t, n.places, d);
      CountOfListNextTerm(n, t, d, lm, m, b, v);
    } else {
      LookupListNextEntriesNone(n, t, n.places, p);
      if InArc(n, p, t.tname).Some? {
        var a := InArc(n, p, t.tname).value;
        FindArcSome(n.inArcs, p, t.tname);
        MemPlaceNamesOfPlaceColor(n, a.aplace, a.acolor);
        assert false;
      }
      if OutArc(n, t.tname, p).Some? {
        var a := OutArc(n, t.tname, p).value;
        FindArcSome(n.outArcs, p, t.tname);
        MemPlaceNamesOfPlaceColor(n, a.aplace, a.acolor);
        assert false;
      }
      CoeffUnion(Diff(m(p), EmptyBag()), EmptyBag(), v);
      CoeffDiff(m(p), EmptyBag(), v);
    }
  }

  // -------------------------------------------------- The two halves of the refinement

  /** A step of the list encoding is a step of the bag encoding. */
  lemma StepOfToLpeListStep(n: Net, lm: ListMarking, m: Marking, a: string, lm': ListMarking)
    requires Valid(n)
    requires ListRel(lm, m)
    requires ListLpeStep(ToLpeList(n), lm, a, lm')
    ensures exists m' :: LpeStep(ToLpe(n), m, a, m') && ListRel(lm', m')
  {
    var s, b: Env :|
      && s in ToLpeList(n).lsummands
      && s.lact == a
      && EnvWfOn(s.lbinder, b)
      && Holds(s.lcond, ListToEnv(lm, b))
      && forall p :: lm'(p) == ListNextMarking(s, lm, b)(p);
    MemListSummandsOf(n, n.transitions, s);
    var t :| t in n.transitions && s == ListSummandOf(n, t);
    HoldsListCondTerm(n, t, lm, m, b);
    var m' := Fire(n, m, t, b);
    forall p ensures BagEquiv(m'(p), Fire(n, m, t, b)(p)) {
    }
    assert Occurs(n, m, t, b, m');
    assert Step(n, m, a, m');
    ToLpeStep(n, m, a, m');
    forall p, v ensures CountOf(lm'(p), v) == Coeff(m'(p), v) {
      CountOfListNextMarking(n, t, lm, m, b, p, v);
    }
    assert LpeStep(ToLpe(n), m, a, m') && ListRel(lm', m');
  }

  /** A step of the bag encoding is a step of the list encoding.
    *
    * Together with `StepOfToLpeListStep` this is the refinement `Implementation/docs/Plan.md` 5
    * says nobody has proved. The list state it produces is one particular representative; any
    * other representative of the same bags would have done, which is the order problem
    * answered. */
  lemma ToLpeListStepOfStep(n: Net, lm: ListMarking, m: Marking, a: string, m': Marking)
    requires Valid(n)
    requires ListRel(lm, m)
    requires LpeStep(ToLpe(n), m, a, m')
    ensures exists lm' :: ListLpeStep(ToLpeList(n), lm, a, lm') && ListRel(lm', m')
  {
    ToLpeStep(n, m, a, m');
    var t, b: Env :|
      && t in n.transitions
      && t.tname == a
      && EnvWfOn(VarOf(n, t), b)
      && Occurs(n, m, t, b, m');
    var s := ListSummandOf(n, t);
    MemListSummandsOf(n, n.transitions, s);
    HoldsListCondTerm(n, t, lm, m, b);
    var lm' := ListNextMarking(s, lm, b);
    assert ListLpeStep(ToLpeList(n), lm, a, lm');
    forall p, v ensures CountOf(lm'(p), v) == Coeff(m'(p), v) {
      CountOfListNextMarking(n, t, lm, m, b, p, v);
    }
  }

  /** The two encodings start in markings that represent the same bags. */
  lemma ListRelInit(n: Net)
    requires Valid(n)
    ensures ListRel(ListLpeInitMarking(ToLpeList(n)), LpeInitMarking(ToLpe(n)))
  {
    forall p, v
      ensures CountOf(ListLpeInitMarking(ToLpeList(n))(p), v)
              == Coeff(LpeInitMarking(ToLpe(n))(p), v)
    {
      if p in PlaceNames(n.places) {
        MemPlaceNamesInv(n.places, p);
        var d :| d in n.places && d.pname == p;
        LookupListInitEntries(n.places, d);
        LookupInitEntries(n.places, d);
        assert FreeVars(d.pinit) == [];
        CoeffBagToList(d.pcolor, d.pinit, JunkEnv(), JunkEnv(), v);
      } else {
        LookupListInitEntriesNone(n.places, p);
        LookupInitEntriesNone(n.places, p);
      }
    }
  }
}
