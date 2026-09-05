/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Net

/-!
# The semantics of a Colored Petri Net

Definitions 6 to 9 of the thesis: when a binding element is enabled, what marking it leads to,
and the reachability graph those two induce.

This is the *reference* side of the comparison. `Cpn2mCrl2/Translate.lean` builds the terms of
Definition 14 without looking at any of it, and `Cpn2mCrl2/Correct.lean` then proves the two
agree. `Proof/MCRL2.lean` explains at length why the translation must not simply be *defined*
as the semantics:

> if the translation were defined as the semantics it is being compared against, the two would be one object under two names and the theorem could not fail

The same discipline is kept here, and it now has more to bite on: the two sides are no longer
two transcriptions of one formula that agree by `rfl`, but a Lean predicate on one side and
the evaluation of an emitted *term* on the other.

## Implementation notes

**A marking is a function from place names to bags.** `Proof/ColoredPetriNets.lean` has
`Marking := (p : P) → Bag (L.val (N.C p))`, dependent on the color of the place. Here the
color is not in the type, so a marking is `String → Bag`; `Marking.Wf` is the corresponding
well-typedness, and validity of the net is what makes it preserved.

**Markings are compared up to `Bag.Equiv`.** `Cpn2mCrl2/Bag.lean` represents a bag by an entry
list that is not normalized, so `M p` and `fire M t b p` can be different lists with the same
coefficients. Definition 1 says a bag *is* its coefficient function, so `Occurs` states the
reached marking coefficient by coefficient rather than as an equality of representations.

**Arc expressions of arcs that do not exist.** Definition 7 evaluates `E(p,t)` for every place
`p`, including places not connected to `t`, while `E` is defined on `A` only.
`Net.consume` and `Net.produce` close that gap with the empty bag, which is the convention
recorded in §2.1.1 of `Thesis/docs/ColoredPetriNets.md` and used the same way by
`Proof/ColoredPetriNets.lean`.

## Main definitions

* `Marking`, `Net.initialMarking` : the state of the net, and `M₀`.
* `Net.Enabled` : Definition 6.
* `Net.fire`, `Net.Occurs` : Definition 7.
* `Net.step` : one transition of the reachability graph of Definition 9.
* `Net.Reachable`, `Net.R` : Definition 8.
-/

namespace Cpn2mCrl2

/-- A marking: a bag of tokens for every place. -/
def Marking := String → Bag

/-- A marking is well-typed when every place holds tokens of its own color. -/
def Marking.Wf (N : Net) (M : Marking) : Prop :=
  ∀ d ∈ N.places, (M d.name).ofColor d.color = true

/-- The environment in which Definition 14's terms are read: the place parameters `s_p` hold
the marking, and the summation variables hold the transition's binding.

This is where the two tuples of Definition 13 are realized. `d : D` is the marking, spread
over one bag-sorted variable per place; `h_t : H_t` is the binding `b`, spread over one
color-sorted variable per element of `Var(t)`. No product sort is needed for either, because
mCRL2 already spells a tuple as a parameter list -- which is why `ExprTy` keeps the two
constructors `Proof/CommonDefinitions.lean` gives it, rather than gaining the product former
`Thesis/docs/LeanFormalization.md` §5.1 expects.

The two halves cannot collide: a net's own variables are all color-sorted
(`Net.Valid.varsAreColors`), so a bag-sorted variable is always a place. -/
def Marking.toEnv (M : Marking) (b : Env) : Env
  | .color c, x => b (.color c) x
  | .bag _, x => M x

@[simp] theorem Marking.toEnv_color (M : Marking) (b : Env) (c : Color) (x : String) :
    M.toEnv b (.color c) x = b (.color c) x := rfl

@[simp] theorem Marking.toEnv_bag (M : Marking) (b : Env) (c : Color) (x : String) :
    M.toEnv b (.bag c) x = M x := rfl

namespace Net

variable (N : Net)

/-! ### The tokens a binding element moves -/

/-- The tokens `t` consumes from `p` under the binding `b`: the value of `E(p, t)`, or the
empty bag when there is no such arc. -/
def consume (t : String) (b : Env) (p : String) : Bag :=
  match N.inArc? p t with
  | some a => Expr.eval a.expr b
  | none => ∅

/-- The tokens `t` produces in `p` under the binding `b`: the value of `E(t, p)`, or the empty
bag when there is no such arc. -/
def produce (t : String) (b : Env) (p : String) : Bag :=
  match N.outArc? t p with
  | some a => Expr.eval a.expr b
  | none => ∅

/-- `M₀ p = I(p)⟨⟩`. The initialization expressions are closed -- `Net.Valid.initClosed` --
so the binding they are evaluated under does not matter, and `Env.junk` is as good as any. -/
def initialMarking : Marking := fun p =>
  match N.places.find? fun d => d.name == p with
  | some d => Expr.eval d.init Env.junk
  | none => ∅

/-! ### Definitions 6 and 7 -/

/-- **Definition 6 (Enabled binding element).**
`(t, b)` is enabled in `M` when the arc expression of every place in `pre(t)` evaluates to a
sub-bag of the tokens in that place, and the guard of `t` evaluates to `True`.

The quantifier ranges over the arcs of `pre(t)` rather than over its places, which is the same
conjunction: `Net.Valid.inArcsNodup` says a place contributes at most one arc. -/
def Enabled (M : Marking) (t : TransDecl) (b : Env) : Prop :=
  (∀ a ∈ N.pre t.name, Expr.eval a.expr b ⊆ M a.place) ∧ Expr.Holds t.guard b

instance (M : Marking) (t : TransDecl) (b : Env) : Decidable (N.Enabled M t b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Definition 7 (Occurring binding element).**
The marking reached when `(t, b)` occurs in `M`: every place loses the tokens `t` consumes
from it and gains the tokens `t` produces in it. -/
def fire (M : Marking) (t : TransDecl) (b : Env) : Marking :=
  fun p => (M p \ N.consume t.name b p) ∪ N.produce t.name b p

/-- `(t, b)` is enabled in `M` and `M'` is the marking it leads to, coefficient by
coefficient. -/
def Occurs (M : Marking) (t : TransDecl) (b : Env) (M' : Marking) : Prop :=
  N.Enabled M t b ∧ ∀ p, Bag.Equiv (M' p) (N.fire M t b p)

/-! ### Definitions 8 and 9 -/

/-- One transition `M -t→ M'` of the reachability graph of Definition 9: some binding makes
`(t, b)` occur from `M` to `M'`. -/
def step (M : Marking) (t : String) (M' : Marking) : Prop :=
  ∃ d ∈ N.transitions, d.name = t ∧ ∃ b : Env, N.Occurs M d b M'

/-- `M'` is directly reachable from `M`. -/
def DirectlyReachable (M M' : Marking) : Prop := ∃ t, N.step M t M'

/-- **Definition 8 (Reachability).**
The transitive -- not reflexive transitive -- closure of direct reachability. §3.5.1 of
`Thesis/docs/ColoredPetriNets.md` explains why Definition 9 depends on that reading, and
`Proof/ColoredPetriNets.lean` transcribes it the same way. -/
inductive Reachable : Marking → Marking → Prop where
  /-- One step. -/
  | single {M M' : Marking} (h : N.DirectlyReachable M M') : Reachable M M'
  /-- One more step at the end of a chain. -/
  | tail {M M' M'' : Marking} (h : Reachable M M') (h' : N.DirectlyReachable M' M'') :
      Reachable M M''

/-- `R(M)`, the set of markings reachable from `M`. -/
def R (M : Marking) : Marking → Prop := fun M' => N.Reachable M M'

end Net

end Cpn2mCrl2
