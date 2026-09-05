/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # Linear Process Equations, as syntax
 *
 * Definitions 13 and 15 of the thesis, with the condition and the next state as *terms*.
 *
 * This is the change `Thesis/docs/LeanFormalization.md` 5 asks for and
 * `Implementation/docs/Plan.md` 4 obligation 5 restates. `Proof/MCRL2.lean` says of its own
 * `LPE`:
 *
 * > With the condition a proposition and the next state a Lean function, an `LPE` is not a
 * > piece of mCRL2 text.
 *
 * Here `Summand.cond` is an `Expr` and `Summand.next` is one bag-valued `Expr` per place, so an
 * `Lpe` *is* a piece of mCRL2 text -- modulo printing, which `src/Print.dfy` does. `LpeStep`
 * below then says what such a specification denotes, and `src/Correct.dfy` proves the
 * denotation is the CPN semantics of Definitions 6 and 7. That is the T2 tier of
 * `Implementation/docs/Plan.md` 2.
 *
 * ## `D` and `H_t` are binder lists, not sorts
 *
 * Definition 13 gives a summand one summation variable `h_k : H_k` and the process one
 * parameter `d : D`, both tuple-sorted. `Thesis/docs/LeanFormalization.md` 5.1 therefore
 * expects `ExprTy` to gain a product former and calls that "the structural blocker"; the
 * reference generator of `Implementation/docs/Target.md` 3 answers it with a `struct` per
 * transition.
 *
 * Neither is needed, and the reason is the same in Dafny as in Lean and has nothing to do with
 * the type system: mCRL2 spells both tuples as parameter lists of its own -- `proc Spec(sp1,
 * sp2, sp3 : Bag(Int))` and `sum h : Int . ...` -- so `Summand.binder` is a context and
 * `Lpe.params` a sequence, and the components are ordinary variables of the unextended
 * `ExprTy`. Obligation 1 of `Implementation/docs/Plan.md` 4 is discharged by choosing the
 * mCRL2 form that already has products rather than by adding products to the data language.
 *
 * Record colors still need `struct`, and `src/Print.dfy` emits them; that is a product in the
 * *data* language, which `src/Color.dfy` has had from the start.
 *
 * ## Main definitions
 *
 * * `Lpe`, `Summand` : Definition 13, syntactically.
 * * `LpeStep` : Definition 15, the transition relation the specification denotes.
 */
module Lpe {

  import opened Std.Wrappers
  import opened Util
  import opened Color
  import opened Bag
  import opened ListOps
  import opened Expr
  import opened Net
  import opened Semantics

  /** A term of bag sort, with the color it is a bag of.
    *
    * The components of `g_t` have one type per place, so the color has to travel with the term
    * for the printer to know which sort to declare. */
  datatype BagTerm = BagTerm(btcolor: Color, btterm: Expr)

  /** One summand of an LPE: `sum_{h_k : H_k} c_k(d, h_k) -> a_k . Spec(g_k(d, h_k))`. */
  datatype Summand = Summand(
    /* `H_k`, as the variables the `sum` binds. */
    binder: Ctx,
    /* `c_k`, as a boolean term over the place parameters and the binder. */
    cond: Expr,
    /* `a_k in Act`, a label carrying no parameters, as the note under Definition 14 records. */
    act: string,
    /* `g_k`, as one bag term per place, keyed by the place's name. A place the sequence does
       not mention keeps its marking. */
    next: seq<(string, BagTerm)>)

  /** **Definition 13 (Linear Process Equation)**, as syntax.
    *
    *     Spec(d : D) = sum_{k in K} sum_{h_k : H_k} c_k(d, h_k) -> a_k . Spec(g_k(d, h_k))
    *
    * `K` is the index of `summands`; `D` is `params`, one bag-sorted parameter per place.
    * `sorts` and `acts` carry what the emitted file has to declare before the process. */
  datatype Lpe = Lpe(
    sorts: seq<Color>,
    params: seq<(string, Color)>,
    acts: seq<string>,
    summands: seq<Summand>,
    init: seq<(string, BagTerm)>)

  /** The condition of the summand, read in a marking under a binding of its summation
    * variables. */
  ghost predicate CondHolds(s: Summand, m: Marking, b: Env)
  {
    Holds(s.cond, ToEnv(m, b))
  }

  /** The marking the summand leads to: each place gets the value of its component of `g_k`, and
    * a place the summand does not mention keeps what it had. */
  ghost function NextMarking(s: Summand, m: Marking, b: Env): Marking
  {
    (p: string) =>
      match Lookup(s.next, p)
      case Some(bt) => AsBag(Eval(bt.btterm, ToEnv(m, b)))
      case None => m(p)
  }

  /** `d0`, evaluated. The initial terms are closed, so the binding is irrelevant. */
  ghost function LpeInitMarking(l: Lpe): Marking
  {
    (p: string) =>
      match Lookup(l.init, p)
      case Some(bt) => AsBag(Eval(bt.btterm, JunkEnv()))
      case None => EmptyBag()
  }

  /** **Definition 15 (Semantics of an LPE).**
    * There is a transition `d -a_k-> d'` whenever some value of the summation variables
    * satisfies the condition of summand `k` and takes `d` to `d'`.
    *
    * `sum v : S . p` binds `v` at the sort `S`, so the summation ranges over environments that
    * are well-typed on the binder and not over arbitrary ones -- which is Definition 15's
    * `b in B[H_k]`, with `B` as Definition 2 defines it.
    *
    * The reached state is compared coefficient by coefficient, for the reason
    * `src/Semantics.dfy` gives: a bag is its coefficient function, not the entry sequence that
    * represents it. */
  ghost predicate LpeStep(l: Lpe, m: Marking, a: string, m': Marking)
  {
    exists s, b: Env ::
      && s in l.summands
      && s.act == a
      && EnvWfOn(s.binder, b)
      && CondHolds(s, m, b)
      && forall p :: BagEquiv(m'(p), NextMarking(s, m, b)(p))
  }
}
