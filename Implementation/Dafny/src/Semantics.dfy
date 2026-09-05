/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # The semantics of a Colored Petri Net
 *
 * Definitions 6 to 9 of the thesis: when a binding element is enabled, what marking it leads
 * to, and the reachability graph those two induce.
 *
 * This is the *reference* side of the comparison. `src/Translate.dfy` builds the terms of
 * Definition 14 without looking at any of it, and `src/Correct.dfy` then proves the two agree.
 * `Proof/MCRL2.lean` explains at length why the translation must not simply be *defined* as the
 * semantics:
 *
 * > if the translation were defined as the semantics it is being compared against, the two
 * > would be one object under two names and the theorem could not fail
 *
 * The same discipline is kept here, and it has the same bite it has in
 * `Implementation/Lean`: the two sides are not two transcriptions of one formula, but a
 * predicate on one side and the evaluation of an emitted *term* on the other.
 *
 * Everything in this file is `ghost`. A marking is a function from place names to bags and the
 * translator never builds one; these definitions exist so that the T2 theorems have a
 * left-hand side.
 *
 * ## Implementation notes
 *
 * **Markings are compared up to `BagEquiv`.** `src/Bag.dfy` represents a bag by an entry
 * sequence that is not normalized, so `M(p)` and `Fire(...)(p)` can be different sequences with
 * the same coefficients. Definition 1 says a bag *is* its coefficient function, so `Occurs`
 * states the reached marking coefficient by coefficient rather than as an equality of
 * representations.
 *
 * **Arc expressions of arcs that do not exist.** Definition 7 evaluates `E(p,t)` for every
 * place `p`, including places not connected to `t`, while `E` is defined on `A` only. `Consume`
 * and `Produce` close that gap with the empty bag, which is the convention recorded in 2.1.1 of
 * `Thesis/docs/ColoredPetriNets.md` and used the same way by `Proof/ColoredPetriNets.lean`.
 *
 * ## Main definitions
 *
 * * `Marking`, `InitialMarking` : the state of the net, and `M0`.
 * * `Enabled` : Definition 6.
 * * `Fire`, `Occurs` : Definition 7.
 * * `Step` : one transition of the reachability graph of Definition 9.
 * * `Reachable`, `R` : Definition 8.
 */
module Semantics {

  import opened Std.Wrappers
  import opened Util
  import opened Color
  import opened Bag
  import opened ListOps
  import opened Expr
  import opened Net

  /** A marking: a bag of tokens for every place. */
  type Marking = string -> Bag

  /** A marking is well-typed when every place holds tokens of its own color. */
  ghost predicate MarkingWf(n: Net, m: Marking)
  {
    forall d :: d in n.places ==> BagOfColor(m(d.pname), d.pcolor)
  }

  /** The environment in which Definition 14's terms are read: the place parameters `s_p` hold
    * the marking, and the summation variables hold the transition's binding.
    *
    * This is where the two tuples of Definition 13 are realized. `d : D` is the marking, spread
    * over one bag-sorted variable per place; `h_t : H_t` is the binding `b`, spread over one
    * color-sorted variable per element of `Var(t)`. No product sort is needed for either,
    * because mCRL2 already spells a tuple as a parameter list -- which is why `ExprTy` keeps
    * the two constructors `Proof/CommonDefinitions.lean` gives it, rather than gaining the
    * product former `Thesis/docs/LeanFormalization.md` 5.1 expects.
    *
    * The two halves cannot collide: a net's own variables are all color-sorted
    * (`VarsAreColors`), so a bag-sorted variable is always a place. The list sort plays no part
    * here -- it belongs to the second backend, and `src/ListEncoding.dfy` has its own
    * environment for it. */
  ghost function ToEnv(m: Marking, b: Env): Env
  {
    (t: ExprTy, x: string) =>
      match t
      case CT(_) => b(t, x)
      case BT(_) => DBag(m(x))
      case LT(_) => DList([])
  }

  lemma ToEnvColor(m: Marking, b: Env, c: Color, x: string)
    ensures ToEnv(m, b)(CT(c), x) == b(CT(c), x)
  {
  }

  lemma ToEnvBag(m: Marking, b: Env, c: Color, x: string)
    ensures ToEnv(m, b)(BT(c), x) == DBag(m(x))
  {
  }

  // ---------------------------------------------------------------------------------------
  // The tokens a binding element moves
  // ---------------------------------------------------------------------------------------

  /** The tokens `t` consumes from `p` under the binding `b`: the value of `E(p, t)`, or the
    * empty bag when there is no such arc. */
  ghost function Consume(n: Net, t: string, b: Env, p: string): Bag
  {
    match InArc(n, p, t)
    case Some(a) => AsBag(Eval(a.aexpr, b))
    case None => EmptyBag()
  }

  /** The tokens `t` produces in `p` under the binding `b`: the value of `E(t, p)`, or the empty
    * bag when there is no such arc. */
  ghost function Produce(n: Net, t: string, b: Env, p: string): Bag
  {
    match OutArc(n, t, p)
    case Some(a) => AsBag(Eval(a.aexpr, b))
    case None => EmptyBag()
  }

  /** `M0(p) = I(p)<>`. The initialization expressions are closed -- `InitClosed` -- so the
    * binding they are evaluated under does not matter, and `JunkEnv()` is as good as any. */
  ghost function InitialMarking(n: Net): Marking
  {
    (p: string) =>
      match FindPlace(n.places, p)
      case Some(d) => AsBag(Eval(d.pinit, JunkEnv()))
      case None => EmptyBag()
  }

  // ---------------------------------------------------------------------------------------
  // Definitions 6 and 7
  // ---------------------------------------------------------------------------------------

  /** **Definition 6 (Enabled binding element).**
    * `(t, b)` is enabled in `M` when the arc expression of every place in `pre(t)` evaluates to
    * a sub-bag of the tokens in that place, and the guard of `t` evaluates to `True`.
    *
    * The quantifier ranges over the arcs of `pre(t)` rather than over its places, which is the
    * same conjunction: `InArcsNoDup` says a place contributes at most one arc. */
  ghost predicate Enabled(n: Net, m: Marking, t: TransDecl, b: Env)
  {
    && (forall a :: a in Pre(n, t.tname) ==> Subset(AsBag(Eval(a.aexpr, b)), m(a.aplace)))
    && Holds(t.guard, b)
  }

  /** **Definition 7 (Occurring binding element).**
    * The marking reached when `(t, b)` occurs in `M`: every place loses the tokens `t` consumes
    * from it and gains the tokens `t` produces in it. */
  ghost function Fire(n: Net, m: Marking, t: TransDecl, b: Env): Marking
  {
    (p: string) => Union(Diff(m(p), Consume(n, t.tname, b, p)), Produce(n, t.tname, b, p))
  }

  /** `(t, b)` is enabled in `M` and `M'` is the marking it leads to, coefficient by
    * coefficient. */
  ghost predicate Occurs(n: Net, m: Marking, t: TransDecl, b: Env, m': Marking)
  {
    Enabled(n, m, t, b) && forall p :: BagEquiv(m'(p), Fire(n, m, t, b)(p))
  }

  // ---------------------------------------------------------------------------------------
  // Definitions 8 and 9
  // ---------------------------------------------------------------------------------------

  /** One transition `M -t-> M'` of the reachability graph of Definition 9: some binding of `t`
    * makes `(t, b)` occur from `M` to `M'`.
    *
    * The binding is quantified over `B(t)`, the bindings of `Var(t)` -- which by Definition 2
    * assign to each variable a value of *its own type*, hence the `EnvWfOn`. `Enabled` itself
    * carries no such condition, because Definition 6 does not: it is a statement about a
    * binding element, and which bindings exist is Definition 2's business. */
  ghost predicate Step(n: Net, m: Marking, t: string, m': Marking)
  {
    exists d, b: Env ::
      && d in n.transitions
      && d.tname == t
      && EnvWfOn(VarOf(n, d), b)
      && Occurs(n, m, d, b, m')
  }

  /** `M'` is directly reachable from `M`. */
  ghost predicate DirectlyReachable(n: Net, m: Marking, m': Marking)
  {
    exists t :: Step(n, m, t, m')
  }

  /** **Definition 8 (Reachability).**
    * The transitive -- not reflexive transitive -- closure of direct reachability. 3.5.1 of
    * `Thesis/docs/ColoredPetriNets.md` explains why Definition 9 depends on that reading, and
    * `Proof/ColoredPetriNets.lean` transcribes it the same way. */
  least predicate Reachable(n: Net, m: Marking, m': Marking)
  {
    || DirectlyReachable(n, m, m')
    || (exists mid :: Reachable(n, m, mid) && DirectlyReachable(n, mid, m'))
  }

  /** `R(M)`, the set of markings reachable from `M`. */
  ghost predicate R(n: Net, m: Marking, m': Marking)
  {
    Reachable(n, m, m')
  }
}
