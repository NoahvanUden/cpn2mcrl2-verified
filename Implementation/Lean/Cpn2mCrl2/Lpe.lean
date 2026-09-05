/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Semantics

/-!
# Linear Process Equations, as syntax

Definitions 13 and 15 of the thesis, with the condition and the next state as *terms*.

This is the change `Thesis/docs/LeanFormalization.md` §5 asks for and
`Implementation/docs/Plan.md` §4 obligation 5 restates. `Proof/MCRL2.lean` says of its own
`LPE`:

> With the condition a proposition and the next state a Lean function, an `LPE` is not a piece of mCRL2 text.

Here `Summand.cond` is an `Expr (.color .bool)` and `Summand.next` is one bag-valued `Expr`
per place, so an `Lpe` *is* a piece of mCRL2 text -- modulo printing, which
`Cpn2mCrl2/Print.lean` does. `Lpe.semantics` below then says what such a specification
denotes, and `Cpn2mCrl2/Correct.lean` proves the denotation is the CPN semantics of
Definitions 6 and 7. That is the T2 tier of `Implementation/docs/Plan.md` §2.

## Implementation notes

**`D` and `H_t` are binder lists, not sorts.** Definition 13 gives a summand one summation
variable `h_k : H_k` and the process one parameter `d : D`, both tuple-sorted.
`Thesis/docs/LeanFormalization.md` §5.1 therefore expects `ExprTy` to gain a product former
and calls that "the structural blocker"; the reference generator of
`Implementation/docs/Target.md` §3 answers it with a `struct` per transition.

Neither is needed. mCRL2 spells both tuples as parameter lists of its own -- `proc Spec(sp1,
sp2, sp3 : Bag(Int))` and `sum h : Int . ...` -- so `Summand.binder` is a context and
`Lpe.params` is a list, and the components are ordinary variables of the *unextended*
`ExprTy`. Obligation 1 of `Implementation/docs/Plan.md` §4 is discharged by choosing the
mCRL2 form that already has products rather than by adding products to the data language.

Record colors still need `struct`, and `Cpn2mCrl2/Print.lean` emits them; that is a product
in the *data* language, which `Cpn2mCrl2/Color.lean` has had from the start.

**The bounded quantifier is gone at this level.** Definition 14's `∀ p ∈ pre(t)` is unfolded
into a finite conjunction when the summand is built, so nothing in `Expr` quantifies. That is
obligation 3 of `Implementation/docs/Plan.md` §4.

**The action carries no parameters.** As the note under Definition 14 records, and as
`Proof/MCRL2.lean` models it: `act` is a label.

## Main definitions

* `Lpe`, `Summand` : Definition 13, syntactically.
* `Lpe.step` : Definition 15, the transition relation the specification denotes.
-/

namespace Cpn2mCrl2

/-- A term of bag sort, with the color it is a bag of.

The components of `g_t` have one type per place, so they cannot go in a homogeneous list
without pairing each with its color. -/
structure BagTerm where
  /-- The color the term is a bag of. -/
  color : Color
  /-- The term. -/
  term : Expr (.bag color)

/-- One summand of an LPE: `∑_{h_k : H_k} c_k(d, h_k) → a_k · Spec(g_k(d, h_k))`. -/
structure Summand where
  /-- `H_k`, as the list of variables the `sum` binds. -/
  binder : Ctx
  /-- `c_k`, as a boolean term over the place parameters and the binder. -/
  cond : Expr (.color .bool)
  /-- `a_k ∈ Act`, a label carrying no parameters. -/
  act : String
  /-- `g_k`, as one bag term per place, keyed by the place's name. A place the list does not
  mention keeps its marking. -/
  next : List (String × BagTerm)

/-- **Definition 13 (Linear Process Equation)**, as syntax.

    Spec(d : D) = ∑_{k ∈ K} ∑_{h_k : H_k} c_k(d, h_k) → a_k · Spec(g_k(d, h_k))

`K` is the index of `summands`; `D` is `params`, one bag-sorted parameter per place. `sorts`
and `acts` carry what the emitted file has to declare before the process. -/
structure Lpe where
  /-- The colors whose sorts the specification declares. -/
  sorts : List Color
  /-- `D`, as one parameter per place with the color it holds a bag of. -/
  params : List (String × Color)
  /-- `Act`, the action labels. -/
  acts : List String
  /-- The summands, indexed by `K`. -/
  summands : List Summand
  /-- `d₀`, as one closed bag term per place. -/
  init : List (String × BagTerm)

namespace Summand

/-- The condition of the summand, read in a marking under a binding of its summation
variables. -/
def condHolds (S : Summand) (M : Marking) (b : Env) : Prop :=
  Expr.Holds S.cond (M.toEnv b)

/-- The marking the summand leads to: each place gets the value of its component of `g_k`, and
a place the summand does not mention keeps what it had. -/
def nextMarking (S : Summand) (M : Marking) (b : Env) : Marking := fun p =>
  match List.lookup p S.next with
  | some bt => Expr.eval bt.term (M.toEnv b)
  | none => M p

end Summand

namespace Lpe

/-- `d₀`, evaluated. The initial terms are closed, so the binding is irrelevant. -/
def initMarking (L : Lpe) : Marking := fun p =>
  match List.lookup p L.init with
  | some bt => Expr.eval bt.term Env.junk
  | none => ∅

/-- **Definition 15 (Semantics of an LPE).**
There is a transition `d -a_k→ d'` whenever some value of the summation variables satisfies
the condition of summand `k` and takes `d` to `d'`.

`sum v : S . p` binds `v` at the sort `S`, so the summation ranges over environments that are
well-typed on the binder and not over arbitrary ones -- which is Definition 15's `b ∈ B[H_k]`,
with `B` as Definition 2 defines it.

The reached state is compared coefficient by coefficient, for the reason
`Cpn2mCrl2/Semantics.lean` gives: a bag is its coefficient function, not the entry list that
represents it. -/
def step (L : Lpe) (M : Marking) (a : String) (M' : Marking) : Prop :=
  ∃ S ∈ L.summands, S.act = a ∧ ∃ b : Env, b.WfOn S.binder ∧
    S.condHolds M b ∧ ∀ p, Bag.Equiv (M' p) (S.nextMarking M b p)

end Lpe

end Cpn2mCrl2
