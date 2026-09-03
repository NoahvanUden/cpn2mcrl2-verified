/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Proof.ColoredPetriNets

/-!
# mCRL2

Definitions 13, 14, 15 and 18 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025), Chapters 5 and 6: the Linear Process Equation, the translation of
a Colored Petri Net into one, the LTS an LPE induces, and the modal mu-calculus.

See `Thesis/docs/mCRL2.md` for the prose version. The rest of that page -- the model
checking pipeline, the shape of counterexamples, and the encoding notes on markings and
strings -- is about the toolset rather than about definitions, and has nothing to formalize.

## Implementation notes

**The condition `c_k` is a predicate, not a `Bool`.** Definition 13 types it as
`c_k : D × H_k → Bool`, which is what an mCRL2 data expression of sort `Bool` is. Here it is
`D → H_k → Prop`. The translation of Definition 14 is the reason: the condition it builds
contains a bag inclusion `E(p, t) ⊆ s_p`, and bag inclusion over an arbitrary color is not
decidable, so it cannot be given as a `Bool` without assuming decidability throughout. A
`Bool`-valued condition is the special case `fun d h => c k d h = true`.

**The action `a_k` is a label.** Definition 13 writes the shape of an LPE with `a_k(d, h_k)`
but lists `a_k ∈ Act` among the components, and Definition 15 uses `a_k` alone as the label
of a transition. It is modelled here as the label `act k ∈ Act`, which is also what the
translation produces: the note under Definition 14 records that the action it emits carries
no parameters.

**`d₀` is not part of the LPE.** Definition 13 does not mention an initial state; Definition
15 introduces it as "for a given `d₀ ∈ D`". So `LPE.semantics` takes it as an argument, and
the translation supplies `CPN.toLPEInit` alongside `CPN.toLPE`.

## Main definitions

* `LPE Act` : Definition 13.
* `LPE.semantics` : Definition 15, the LTS induced by an LPE.
* `CPN.toLPE`, `CPN.toLPEInit` : Definition 14, the translation of a CPN.
* `MuFormula` : Definition 18, the syntax of the modal mu-calculus.
-/

universe u v w x y

/-! ## Linear Process Equations -/

/-- **Definition 13 (Linear Process Equation (LPE)).**
An LPE is a specification of the shape

    Spec(d : D) = ∑_{k ∈ K} ∑_{h_k : H_k} c_k(d, h_k) → a_k · Spec(g_k(d, h_k))

given by a datatype `D` of states, an index set `K`, and for each `k ∈ K` a datatype `H_k`
of summation variables, a condition `c_k`, an action label `a_k ∈ Act` and a next state
`g_k`.

The summation `∑_{k ∈ K}` of Section 1.2 is a shorthand for the choice between the
summands, so an LPE is exactly the family of summands indexed by `K`. -/
structure LPE (Act : Type u) where
  /-- `D`, the datatype of the state. -/
  D : Type v
  /-- `K`, the index set of the summands. -/
  K : Type w
  /-- `H_k`, the datatype summed over in summand `k`. -/
  H : K → Type x
  /-- `c_k : D × H_k → Bool`, the condition of summand `k`. -/
  cond : (k : K) → D → H k → Prop
  /-- `a_k ∈ Act`, the action label of summand `k`. -/
  act : K → Act
  /-- `g_k : D × H_k → D`, the next state of summand `k`. -/
  next : (k : K) → D → H k → D

namespace LPE

variable {Act : Type u}

/-- **Definition 15 (Semantics of LPE).**
The LTS `(S, L, →, s₀)` induced by an LPE with a given initial state `d₀`: the states are
`D`, the actions are `Act`, the initial state is `d₀`, and there is a transition
`d -a_k→ d'` whenever some value of the summation variable `h_k` satisfies the condition of
summand `k` and takes `d` to `d'`.

Definition 15 writes the source of a transition as `d⟨b⟩` for a binding `b ∈ B[H_k]`. A
state of this LTS is already a value of `D` and `b` assigns a value to the summation
variable `h_k` only, so `d⟨b⟩` is `d`; the binding is the `h` quantified over here. -/
def semantics (Spec : LPE Act) (d₀ : Spec.D) : LTS Spec.D Act where
  step d a d' := ∃ (k : Spec.K) (h : Spec.H k),
    Spec.act k = a ∧ Spec.cond k d h ∧ d' = Spec.next k d h
  init := d₀

end LPE

/-! ## Translating a CPN to an LPE -/

namespace CPN

variable {L : ExprLang.{u, v, w, x}} {P T : Type y} (N : CPN L P T)

/-- **Definition 14 (Translation).**
The LPE produced from a CPN: the index set `K` is the set of transitions `T`, the state `D`
is the tuple of bags of tokens holding one bag per place, `H_t` is the tuple of values of
the variables of `t`, and `a_t` is `t` itself, carrying no parameters.

`D` is `N.Marking` and `H_t` is `N.TransBinding t`: the tuple `(S_{p₁} × … × S_{pₙ})` with
one component per place *is* a marking, and the tuple `(Type[v₁] × … × Type[vₙ])` over
`v ∈ Var(t)` *is* a binding of `Var(t)`, which is what `B[H_t]` ranges over in Definition 15.

Definition 14 spells `c_t` and `g_t` out as

    c_t(d, h_t) = (∀ p ∈ pre(t) : E(p,t) ⊆ s_p) ∧ G(t)
    g_t(d, h_t) = ((s_{p₁} \ E(p₁,t)) ∪ E(t,p₁), …, (s_{pₙ} \ E(pₙ,t)) ∪ E(t,pₙ))

and both are written out here, from Definition 14's own text.

They could instead have been given by `Enabled` and `fire`: the two right-hand sides above
are, symbol for symbol, the enabledness condition of Definition 6 and the marking reached in
Definition 7, as Section 1.3 of the notes says they should be. That is deliberately *not*
done. Theorem 1 is the claim that the reachability graph of Definition 9 and the LTS this
translation induces have the same behavior; if the translation were defined as the semantics
it is being compared against, the two would be one object under two names and the theorem
could not fail -- a slip introduced into `Enabled` (quantifying over `post(t)` rather than
`pre(t)`, say, which is the slip the thesis itself makes) would change both sides together
and still typecheck.

Keeping them separate makes the identification a claim instead: `toLPE_cond` and
`toLPE_next` below. Both still hold by `rfl`, since the two are transcriptions of the same
formula, but `rfl` stops typechecking as soon as either side drifts from the other.

What *is* shared with Definitions 6 and 7 is how the components of the CPN are read:
`pre`, `G`, and `consume`/`produce` for the convention of Section 2.1.1 on arc expressions of
non-existing arcs. Those are the interpretation of `E` and `G` themselves, not part of the
translation, and Definition 14 refers to them exactly as Definitions 6 and 7 do. -/
noncomputable def toLPE : LPE T where
  D := N.Marking
  K := T
  H := N.TransBinding
  cond t d b :=
    (∀ (p : P) (h : p ∈ N.pre t), consumedBy b p h ⊆ d p) ∧
      ExprLang.Holds (N.G t).1 (N.vars_G_subset t) b
  act := id
  next t d b := fun p => (d p \ consume (t := t) b p) ∪ produce (t := t) b p

@[simp] theorem toLPE_K : N.toLPE.K = T := rfl

@[simp] theorem toLPE_D : N.toLPE.D = N.Marking := rfl

@[simp] theorem toLPE_H (t : T) : N.toLPE.H t = N.TransBinding t := rfl

@[simp] theorem toLPE_act (t : T) : N.toLPE.act t = t := rfl

/-- The condition `c_t` that Definition 14 builds is the enabledness of `(t, b)` in `d` of
Definition 6.

This and `toLPE_next` are the two halves of "the translation computes the semantics", and
they carry the content that the definition of `toLPE` deliberately does not assume. -/
@[simp] theorem toLPE_cond (t : T) (d : N.Marking) (b : N.TransBinding t) :
    N.toLPE.cond t d b = Enabled d b := rfl

/-- The next state `g_t` that Definition 14 builds is the marking that `(t, b)` leads to in
Definition 7. -/
@[simp] theorem toLPE_next (t : T) (d : N.Marking) (b : N.TransBinding t) :
    N.toLPE.next t d b = fire d b := rfl

/-- The initial state `d₀ = (M₀(p₁), …, M₀(pₙ))` of the translated LPE, which is the initial
marking of the CPN. -/
noncomputable def toLPEInit : N.toLPE.D := N.initialMarking

/-- The LTS induced by the translation of a CPN: Definition 15 applied to Definition 14. -/
noncomputable def toLPESemantics : LTS N.Marking T := N.toLPE.semantics N.toLPEInit

/-- A transition of the induced LTS is a binding element occurring, without the restriction
to reachable markings that the reachability graph of Definition 9 carries. -/
theorem toLPESemantics_step (d : N.Marking) (t : T) (d' : N.Marking) :
    N.toLPESemantics.step d t d' ↔ ∃ b : N.TransBinding t, Occurs d b d' := by
  constructor
  · rintro ⟨k, b, rfl, hc, rfl⟩
    exact ⟨b, hc, rfl⟩
  · rintro ⟨b, hc, rfl⟩
    exact ⟨t, b, rfl, hc, rfl⟩

end CPN

/-! ## The modal mu-calculus -/

/-- **Definition 18 (the modal mu-calculus).**
The syntax of the mu-calculus in its basic form, over the actions `L` of an LTS and a set
`Var` of fixpoint variables:

    φ ::= false | true | ¬φ | φ ∨ φ | φ ∧ φ | ⟨a⟩φ | [a]φ | μX.φ | νX.φ | X

The thesis requires, so that the fixpoints `μX.φ` and `νX.φ` exist, that every occurrence of
`X` in `φ` is preceded by an even number of negations. That is a side condition on formulas,
not part of the grammar, and it is not enforced by this datatype; the thesis defines no
semantics for the logic, so nothing here depends on it. -/
inductive MuFormula (L : Type u) (Var : Type v) where
  /-- `false`. -/
  | false
  /-- `true`. -/
  | true
  /-- `¬φ`. -/
  | neg (φ : MuFormula L Var)
  /-- `φ ∨ ψ`. -/
  | or (φ ψ : MuFormula L Var)
  /-- `φ ∧ ψ`. -/
  | and (φ ψ : MuFormula L Var)
  /-- `⟨a⟩φ`, the action `a` can be done, reaching a state satisfying `φ`. -/
  | dia (a : L) (φ : MuFormula L Var)
  /-- `[a]φ`, every `a` step reaches a state satisfying `φ`. -/
  | box (a : L) (φ : MuFormula L Var)
  /-- `μX.φ`, the least fixpoint. -/
  | mu (X : Var) (φ : MuFormula L Var)
  /-- `νX.φ`, the greatest fixpoint. -/
  | nu (X : Var) (φ : MuFormula L Var)
  /-- A fixpoint variable. -/
  | var (X : Var)
  deriving Repr

namespace MuFormula

variable {L : Type u} {Var : Type v}

/-! ### Shorthand notation

Section 2.2 of the notes writes the shorthands over a finite set of actions `A ⊆ L`. A
finite set of actions is given here as a `List L`, which fixes the order and the bracketing
of the disjunction `⋁_{a ∈ A}` and the conjunction `⋀_{a ∈ A}` that the thesis leaves
unspecified. The empty list gives the empty disjunction `false` and the empty conjunction
`true`. -/

/-- `⟨A⟩φ = ⋁_{a ∈ A} ⟨a⟩φ`. -/
def diaSet : List L → MuFormula L Var → MuFormula L Var
  | [], _ => .false
  | a :: as, φ => .or (.dia a φ) (diaSet as φ)

/-- `[A]φ = ⋀_{a ∈ A} [a]φ`. -/
def boxSet : List L → MuFormula L Var → MuFormula L Var
  | [], _ => .true
  | a :: as, φ => .and (.box a φ) (boxSet as φ)

/-- `⟨A*⟩φ = μX.(⟨A⟩X ∨ φ)`. The fixpoint variable is a parameter here; the thesis leaves
the choice of a fresh `X` implicit. -/
def diaStar (X : Var) (A : List L) (φ : MuFormula L Var) : MuFormula L Var :=
  .mu X (.or (diaSet A (.var X)) φ)

/-- `[A*]φ = νX.([A]X ∧ φ)`. -/
def boxStar (X : Var) (A : List L) (φ : MuFormula L Var) : MuFormula L Var :=
  .nu X (.and (boxSet A (.var X)) φ)

section Complement

variable [DecidableEq L]

/-- `⟨Ā⟩φ = ⟨L \ A⟩φ`. The actions `L` have to be given as a list `all`: the notes write the
complement against the whole action set, which presupposes an enumeration of it. Writing
*true* in place of a set of actions, as Section 2.2 does for the complete set `L`, is
passing `all` itself. -/
def diaCompl (all A : List L) (φ : MuFormula L Var) : MuFormula L Var :=
  diaSet (all.filter fun a => decide (a ∉ A)) φ

/-- `[Ā]φ = [L \ A]φ`. -/
def boxCompl (all A : List L) (φ : MuFormula L Var) : MuFormula L Var :=
  boxSet (all.filter fun a => decide (a ∉ A)) φ

end Complement

end MuFormula
