/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Correctness of the translation
 *
 * Tier T2 of `Implementation/docs/Plan.md` 2:
 *
 * > The emitted LPE term *denotes* the `c_t` and `g_t` of Definition 14.
 *
 * `Proof/MCRL2.lean` has the same two statements, `toLPE_cond` and `toLPE_next`, and both hold
 * there by `rfl`, because both sides are transcriptions of one formula.
 * `Thesis/docs/LeanFormalization.md` 5.1 says what has to change for them to stop being
 * bookkeeping:
 *
 * > `LPE.cond` and `LPE.next` become terms and `LPE.semantics` denotes them, so `toLPE_cond`
 * > and `toLPE_next` stop holding by `rfl` and become theorems proved from the evaluation
 * > equations.
 *
 * That is what `ToLpeCond` and `ToLpeNext` are here. Neither is definitional. Each is proved
 * from the evaluation equations of `src/Expr.dfy`, from the coefficient laws of `src/Bag.dfy`
 * -- `SubsetBIff` is what makes the emitted `subseteq` a `Bool`-valued term at all, which is
 * `Implementation/docs/Plan.md` 4.1 -- and from `EvalCongr`, obligation 4, which is where the
 * place parameters and the summation variables are separated.
 *
 * `ToLpeStep` composes the two: one step of the LTS the emitted specification denotes is one
 * step of the CPN's reachability graph, and conversely.
 *
 * ## What this does and does not establish
 *
 * It establishes T2. Composed with Theorem 1 -- `CPN.bisimulation_transRel` of
 * `Proof/Soundness.lean`, tier T3, already proved -- it is the statement
 * `Implementation/docs/Plan.md` 2 calls "the theorem the project is for". That composition is
 * **not** carried out mechanically here and cannot be:
 * `Implementation/docs/Languages.md` 3 says so when it picks Dafny second --
 *
 * > the resulting proof will not connect to Theorem 1 except on paper
 *
 * -- and `Implementation/Lean/Bridge` is where the composition exists as a term. What this
 * package gives is the same T2 statement, proved independently, about a translator that emits
 * the same text. See `README.md` 5 for what that is worth and what it is not.
 *
 * It does not establish T0 or T4 -- that `mcrl22lps` accepts the printed text, and that what
 * the tool reads back denotes the term that was printed. `Implementation/docs/Plan.md` 2 calls
 * those "the honest ceiling", and `scripts/check.sh` tests them.
 *
 * ## Main results
 *
 * * `ToLpeCond` : the emitted condition denotes Definition 6's enabledness.
 * * `ToLpeNext` : the emitted next-state term denotes Definition 7's marking.
 * * `ToLpeStep` : the two transition relations agree.
 */
module Correct {

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

  // ---------------------------------------------------------------------------------------
  // The two environments agree where an expression can see
  //
  // The place parameters and the summation variables are separate halves of `ToEnv`, and a
  // CPN's own expressions only ever mention the second half -- `VarsAreColors`. This is
  // obligation 4 of `Implementation/docs/Plan.md` 4 in the form the translation needs it.
  // ---------------------------------------------------------------------------------------

  lemma AgreeOnVars(n: Net, m: Marking, b: Env)
    requires VarsAreColors(n)
    ensures forall q :: q in n.vars ==> ToEnv(m, b)(q.1, q.0) == b(q.1, q.0)
  {
    forall q | q in n.vars ensures ToEnv(m, b)(q.1, q.0) == b(q.1, q.0) {
      assert IsColorSort(q.1);
    }
  }

  lemma EvalToEnv(n: Net, e: Expr, m: Marking, b: Env)
    requires Valid(n)
    requires ScopedIn(n.vars, e)
    ensures Eval(e, ToEnv(m, b)) == Eval(e, b)
  {
    AgreeOnVars(n, m, b);
    EvalCongrScoped(n.vars, e, ToEnv(m, b), b);
  }

  lemma HoldsToEnv(n: Net, e: Expr, m: Marking, b: Env)
    requires Valid(n)
    requires ScopedIn(n.vars, e)
    ensures Holds(e, ToEnv(m, b)) <==> Holds(e, b)
  {
    EvalToEnv(n, e, m, b);
  }

  // ---------------------------------------------------------------------------------------
  // `c_t`
  // ---------------------------------------------------------------------------------------

  /** One conjunct of the emitted condition denotes one conjunct of Definition 6.
    *
    * `SubsetBIff` is the step that needs finite support: the emitted `subseteq` is a
    * `Bool`-valued term, and `Implementation/docs/Plan.md` 4.1 records that this is only
    * possible because bags here are finitely supported. */
  lemma HoldsCondConjunct(n: Net, a: ArcDecl, m: Marking, b: Env)
    requires Valid(n)
    requires a in n.inArcs
    ensures Holds(CondConjunct(a), ToEnv(m, b))
            <==> Subset(AsBag(Eval(a.aexpr, b)), m(a.aplace))
  {
    var env := ToEnv(m, b);
    assert Eval(EVar(a.aplace, BT(a.acolor)), env) == DBag(m(a.aplace));
    EvalToEnv(n, a.aexpr, m, b);
    assert Eval(CondConjunct(a), env)
           == DVal(VBool(SubsetB(AsBag(Eval(a.aexpr, b)), m(a.aplace))));
    SubsetBIff(AsBag(Eval(a.aexpr, b)), m(a.aplace));
  }

  /** **`c_t` denotes Definition 6.**
    *
    * `Proof/MCRL2.lean`'s `toLPE_cond` is `rfl`; this one is not. It is proved from the
    * evaluation equations of `Expr`, from `SubsetBIff`, and from obligation 4 in the form
    * `EvalToEnv`. */
  lemma ToLpeCond(n: Net, t: TransDecl, m: Marking, b: Env)
    requires Valid(n)
    requires t in n.transitions
    ensures Holds(CondTerm(n, t), ToEnv(m, b)) <==> Enabled(n, m, t, b)
  {
    var arcs := Pre(n, t.tname);
    var es := CondConjuncts(arcs) + [t.guard];
    HoldsAndAll(es, ToEnv(m, b));
    HoldsToEnv(n, t.guard, m, b);
    assert t.guard in es;

    forall a | a in arcs
      ensures CondConjunct(a) in es
      ensures Holds(CondConjunct(a), ToEnv(m, b))
              <==> Subset(AsBag(Eval(a.aexpr, b)), m(a.aplace))
    {
      MemCondConjuncts(arcs, CondConjunct(a));
      MemInArcsOfMemPre(n, t.tname, a);
      HoldsCondConjunct(n, a, m, b);
    }

    if Enabled(n, m, t, b) {
      forall e | e in es ensures Holds(e, ToEnv(m, b)) {
        if e != t.guard {
          MemCondConjuncts(arcs, e);
          var a :| a in arcs && e == CondConjunct(a);
        }
      }
    }
  }

  // ---------------------------------------------------------------------------------------
  // `g_t`
  // ---------------------------------------------------------------------------------------

  lemma EvalConsumeTerm(n: Net, t: TransDecl, d: PlaceDecl, m: Marking, b: Env)
    requires Valid(n)
    requires d in n.places
    ensures AsBag(Eval(ConsumeTerm(n, t, d), ToEnv(m, b))) == Consume(n, t.tname, b, d.pname)
  {
    match InArc(n, d.pname, t.tname)
    case None =>
    case Some(a) =>
      InArcColor(n, d, t.tname, a);
      EvalToEnv(n, a.aexpr, m, b);
  }

  lemma EvalProduceTerm(n: Net, t: TransDecl, d: PlaceDecl, m: Marking, b: Env)
    requires Valid(n)
    requires d in n.places
    ensures AsBag(Eval(ProduceTerm(n, t, d), ToEnv(m, b))) == Produce(n, t.tname, b, d.pname)
  {
    match OutArc(n, t.tname, d.pname)
    case None =>
    case Some(a) =>
      OutArcColor(n, d, t.tname, a);
      EvalToEnv(n, a.aexpr, m, b);
  }

  /** **`g_t` denotes Definition 7.**
    *
    * The component of the emitted next state for a place evaluates to the bag Definition 7 puts
    * in that place. Like `ToLpeCond`, and unlike `Proof/MCRL2.lean`'s `toLPE_next`, this is not
    * definitional. */
  lemma ToLpeNext(n: Net, t: TransDecl, d: PlaceDecl, m: Marking, b: Env)
    requires Valid(n)
    requires d in n.places
    ensures AsBag(Eval(NextTerm(n, t, d), ToEnv(m, b))) == Fire(n, m, t, b)(d.pname)
  {
    var env := ToEnv(m, b);
    assert Eval(EVar(d.pname, BT(d.pcolor)), env) == DBag(m(d.pname));
    EvalConsumeTerm(n, t, d, m, b);
    EvalProduceTerm(n, t, d, m, b);
  }

  // ---------------------------------------------------------------------------------------
  // The two transition relations
  // ---------------------------------------------------------------------------------------

  /** A place the summand does not mention keeps its marking, and Definition 7 agrees, because
    * every arc of a valid net names a place. */
  lemma NextMarkingEquivFire(n: Net, t: TransDecl, m: Marking, b: Env, p: string)
    requires Valid(n)
    ensures BagEquiv(NextMarking(SummandOf(n, t), m, b)(p), Fire(n, m, t, b)(p))
  {
    if p in PlaceNames(n.places) {
      MemPlaceNamesInv(n.places, p);
      var d :| d in n.places && d.pname == p;
      LookupNextEntries(n, t, n.places, d);
      ToLpeNext(n, t, d, m, b);
    } else {
      LookupNextEntriesNone(n, t, n.places, p);
      // No arc can name `p`, since every arc of a valid net names a place.
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
      forall v ensures Coeff(m(p), v) == Coeff(Fire(n, m, t, b)(p), v) {
        CoeffUnion(Diff(m(p), EmptyBag()), EmptyBag(), v);
        CoeffDiff(m(p), EmptyBag(), v);
      }
    }
  }

  /** **T2, composed.**
    * One transition of the LTS the emitted specification denotes is one transition of the CPN's
    * reachability graph, and conversely.
    *
    * This is the statement `Implementation/docs/Plan.md` 2 puts one composition away from the
    * theorem the project is for: with Theorem 1 of `Proof/Soundness.lean` on the other side,
    * the specification this program prints denotes an LTS bisimilar to the CPN's reachability
    * graph. */
  lemma ToLpeStep(n: Net, m: Marking, a: string, m': Marking)
    requires Valid(n)
    ensures LpeStep(ToLpe(n), m, a, m') <==> Step(n, m, a, m')
  {
    if LpeStep(ToLpe(n), m, a, m') {
      var s, b: Env :|
        && s in ToLpe(n).summands
        && s.act == a
        && EnvWfOn(s.binder, b)
        && CondHolds(s, m, b)
        && forall p :: BagEquiv(m'(p), NextMarking(s, m, b)(p));
      MemSummandsOf(n, n.transitions, s);
      var t :| t in n.transitions && s == SummandOf(n, t);
      ToLpeCond(n, t, m, b);
      forall p ensures BagEquiv(m'(p), Fire(n, m, t, b)(p)) {
        NextMarkingEquivFire(n, t, m, b, p);
        EquivTrans(m'(p), NextMarking(s, m, b)(p), Fire(n, m, t, b)(p));
      }
      assert Occurs(n, m, t, b, m');
      assert Step(n, m, a, m');
    }
    if Step(n, m, a, m') {
      var t, b: Env :|
        && t in n.transitions
        && t.tname == a
        && EnvWfOn(VarOf(n, t), b)
        && Occurs(n, m, t, b, m');
      var s := SummandOf(n, t);
      MemSummandsOf(n, n.transitions, s);
      ToLpeCond(n, t, m, b);
      forall p ensures BagEquiv(m'(p), NextMarking(s, m, b)(p)) {
        NextMarkingEquivFire(n, t, m, b, p);
        EquivSymm(NextMarking(s, m, b)(p), Fire(n, m, t, b)(p));
        EquivTrans(m'(p), Fire(n, m, t, b)(p), NextMarking(s, m, b)(p));
      }
      assert LpeStep(ToLpe(n), m, a, m');
    }
  }
}
