/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Mathlib.Data.Set.Lattice
import Proof.CommonDefinitions
import Proof.LabeledTransitionSystems

/-!
# Colored Petri Nets

Definitions 4 to 9 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025), Chapter 3.

See `Thesis/docs/ColoredPetriNets.md` for the prose version, which also records the two
places where these notes depart from the printed text; both are marked below.

## Implementation notes

The places `P` and the transitions `T` are Lean types and are parameters of `PetriNet` and
`CPN`, as the states and actions are for `LTS`. Their finiteness is a field. Taking them as
two separate types also discharges the condition `P ∩ T = ∅` of Definition 4 by
construction: a place and a transition can never be equal, because they do not have a
common type.

Definition 4 has one set of arcs `A ⊆ (P × T) ∪ (T × P)`; it is split here into the two
sides `inArc` and `outArc` of that union, which is the same data.

The colors, variables and expressions come from an ambient `ExprLang` (see
`Proof/CommonDefinitions.lean`), of which a CPN selects a finite set of colors `colors` and
a finite set of variables `V`.

## Main definitions

* `PetriNet P T` : Definition 4.
* `CPN L P T` : Definition 5.
* `CPN.Enabled`, `CPN.fire`, `CPN.Occurs` : Definitions 6 and 7.
* `CPN.Reachable`, `CPN.R` : Definition 8.
* `CPN.reachabilityGraph` : Definition 9, as an `LTS`.
-/

universe u v w x y

/-! ## Petri Nets -/

/-- **Definition 4 (Petri Net (PN)).**
A Petri Net is a triple `(P, T, A)`, where `P` is a finite set of places, `T` is a finite
set of transitions disjoint from `P`, and `A ⊆ (P × T) ∪ (T × P)` is a set of arcs.

`P` and `T` are the parameters of the structure. Their disjointness is automatic, and the
arc set is given by its two sides: `inArc` for the arcs from a place to a transition, and
`outArc` for the arcs from a transition to a place. -/
structure PetriNet (P : Type u) (T : Type v) where
  /-- `P` is a finite set of places. -/
  finitePlaces : Finite P
  /-- `T` is a finite set of transitions. -/
  finiteTransitions : Finite T
  /-- The arcs from a place to a transition. -/
  inArc : Set (P × T)
  /-- The arcs from a transition to a place. -/
  outArc : Set (T × P)

/-! ## Colored Petri Nets -/

/-- **Definition 5 (Colored Petri Net (CPN)).**
A CPN is a tuple `(P, T, A, Σ, V, C, E, G, I)` consisting of a Petri Net `(P, T, A)`, a
finite set of colors `Σ`, a finite set of typed variables `V`, a function `C` assigning a
color to each place, a guard function `G`, an arc expression function `E`, and an
initialization function `I`.

The arc expression function is split along the two sides of the arc set, as `Ein` and
`Eout`; both take the arc's membership proof, since `E` is defined on `A` only. The typing
conditions on `G`, `E` and `I` are carried by the types of those fields rather than stated
as side conditions: `G t` is a boolean expression, `Ein (p, t)` and `Eout (t, p)` are
expressions of type `C(p)_MS`, and `I p` is a closed expression of type `C(p)_MS`. -/
structure CPN (L : ExprLang.{u, v, w, x}) (P : Type y) (T : Type y) extends PetriNet P T where
  /-- `Σ`, a finite set of colors. -/
  colors : Set L.Color
  /-- `Σ` is finite. -/
  finiteColors : colors.Finite
  /-- The set of colors contains at least the type `Bool`. -/
  boolMem : L.boolColor ∈ colors
  /-- `V`, a finite set of typed variables. -/
  V : Set L.Var
  /-- `V` is finite. -/
  finiteV : V.Finite
  /-- The type of a variable of the net is one of the colors of the net, which is the
  condition `Type[v] ∈ Σ` for all `v ∈ V` of Definition 5. -/
  varTypeMem : ∀ v ∈ V, L.varType v ∈ colors
  /-- `C`, assigning a color to each place. -/
  C : P → L.Color
  /-- The color of a place is one of the colors of the net. -/
  colorMem : ∀ p, C p ∈ colors
  /-- `G`, the guard function, assigning a boolean guard to each transition. -/
  G : (t : T) → L.ExprOn V (.color L.boolColor)
  /-- `E` on the arcs from a place to a transition. -/
  Ein : (a : P × T) → a ∈ inArc → L.ExprOn V (.bag (C a.1))
  /-- `E` on the arcs from a transition to a place. -/
  Eout : (a : T × P) → a ∈ outArc → L.ExprOn V (.bag (C a.2))
  /-- `I`, the initialization function, assigning a closed expression to each place. -/
  I : (p : P) → L.ExprOn ∅ (.bag (C p))

namespace CPN

variable {L : ExprLang.{u, v, w, x}} {P T : Type y} (N : CPN L P T)

/-! ### Preset, postset and marking -/

/-- The preset of a transition `t`: the places that have an outgoing arc to `t`. -/
def pre (t : T) : Set P := {p | (p, t) ∈ N.inArc}

/-- The postset of a transition `t`: the places that have an incoming arc from `t`. -/
def post (t : T) : Set P := {p | (t, p) ∈ N.outArc}

/-- A marking maps each place `p` to a bag of tokens of the color of `p`, and represents
the state of the model. -/
def Marking : Type _ := (p : P) → Bag (L.val (N.C p))

/-- The initial marking, `M₀ p = I(p)⟨⟩`. -/
def initialMarking : N.Marking := fun p => ExprLang.evalClosed (N.I p)

/-! ### Variables and bindings of a transition -/

/-- `Var(t)`, the free variables appearing in the guard of `t` and in the arc expressions
of the arcs connected to `t`. -/
def Var (t : T) : Set L.Var :=
  L.vars (N.G t).1 ∪
      (⋃ (p : P), ⋃ (h : (p, t) ∈ N.inArc), L.vars (N.Ein (p, t) h).1) ∪
    (⋃ (p : P), ⋃ (h : (t, p) ∈ N.outArc), L.vars (N.Eout (t, p) h).1)

theorem vars_G_subset (t : T) : L.vars (N.G t).1 ⊆ N.Var t :=
  fun _ hx => Or.inl (Or.inl hx)

theorem vars_Ein_subset {p : P} {t : T} (h : (p, t) ∈ N.inArc) :
    L.vars (N.Ein (p, t) h).1 ⊆ N.Var t :=
  fun _ hx => Or.inl (Or.inr (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨h, hx⟩⟩))

theorem vars_Eout_subset {p : P} {t : T} (h : (t, p) ∈ N.outArc) :
    L.vars (N.Eout (t, p) h).1 ⊆ N.Var t :=
  fun _ hx => Or.inr (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨h, hx⟩⟩)

/-- `B(t)`, the bindings of a transition `t`: the bindings of all its free variables. A
binding element `(t, b)` is a transition `t` together with a `b : N.TransBinding t`.

Marked `@[reducible]`, like `ExprTy.Value`, so that a binding of `t` is recognised as a
binding of `Var(t)` without unfolding: the evaluation equations of `CPN.Term` and `CPN.Cond`
are stated for an arbitrary set of variables and applied to `Var(t)`. -/
@[reducible] def TransBinding (t : T) : Type _ := L.Binding (N.Var t)

variable {N}

/-- The value of the arc expression `E(p, t)` under a binding of `t`. -/
def consumedBy {t : T} (b : N.TransBinding t) (p : P) (h : (p, t) ∈ N.inArc) :
    Bag (L.val (N.C p)) :=
  ExprLang.evalOn (N.Ein (p, t) h).1 (N.vars_Ein_subset h) b

/-- The value of the arc expression `E(t, p)` under a binding of `t`. -/
def producedBy {t : T} (b : N.TransBinding t) (p : P) (h : (t, p) ∈ N.outArc) :
    Bag (L.val (N.C p)) :=
  ExprLang.evalOn (N.Eout (t, p) h).1 (N.vars_Eout_subset h) b

open Classical in
/-- The tokens `t` consumes from `p` under the binding `b`, for an arbitrary place `p`.

Definition 7 evaluates `E(p, t)` for all `p ∈ P`, including places that are not connected
to `t`, while `E` is defined on `A` only. This uses the convention of Section 2.1.1 of the
notes to close that gap. -/
noncomputable def consume {t : T} (b : N.TransBinding t) (p : P) : Bag (L.val (N.C p)) :=
  if h : (p, t) ∈ N.inArc then consumedBy b p h else ∅

open Classical in
/-- The tokens `t` produces in `p` under the binding `b`, for an arbitrary place `p`, read
with the same convention as `consume`. -/
noncomputable def produce {t : T} (b : N.TransBinding t) (p : P) : Bag (L.val (N.C p)) :=
  if h : (t, p) ∈ N.outArc then producedBy b p h else ∅

/-! ### Enabledness and occurrence -/

/-- **Definition 6 (Enabled binding element).**
A binding element `(t, b)` is enabled in marking `M` if and only if the arc expression of
every place in the preset of `t` evaluates to a sub-bag of the tokens in that place, and
the guard of `t` evaluates to `True`. -/
def Enabled (M : N.Marking) {t : T} (b : N.TransBinding t) : Prop :=
  (∀ (p : P) (h : p ∈ N.pre t), consumedBy b p h ⊆ M p) ∧
    ExprLang.Holds (N.G t).1 (N.vars_G_subset t) b

/-- **Definition 7 (Occurring binding element).**
The marking reached when the binding element `(t, b)` occurs in marking `M`: every place
loses the tokens that `t` consumes from it and gains the tokens that `t` produces in it.
Definition 7 determines this marking uniquely, so it is given here as a function. -/
noncomputable def fire (M : N.Marking) {t : T} (b : N.TransBinding t) : N.Marking :=
  fun p => (M p \ consume b p) ∪ produce b p

/-- The places outside `pre(t) ∪ post(t)` keep their marking when `t` occurs, which is what
the convention on arc expressions of non-existing arcs is for. -/
theorem fire_of_not_mem (M : N.Marking) {t : T} (b : N.TransBinding t) {p : P}
    (hin : (p, t) ∉ N.inArc) (hout : (t, p) ∉ N.outArc) : fire M b p = M p := by
  classical
  ext s
  simp [fire, consume, produce, hin, hout]

/-- Occurrence of a binding element: `(t, b)` is enabled in `M`, and `M'` is the marking it
leads to. -/
def Occurs (M : N.Marking) {t : T} (b : N.TransBinding t) (M' : N.Marking) : Prop :=
  Enabled M b ∧ M' = fire M b

/-! ### Reachability -/

/-- `M'` is directly reachable from `M`: some binding element can occur from `M` to `M'`. -/
def DirectlyReachable (M M' : N.Marking) : Prop :=
  ∃ (t : T) (b : N.TransBinding t), Occurs M b M'

/-- **Definition 8 (Reachability).**
`M'` is reachable from `M` if there are markings `M₁ … Mₙ` with
`M ↠ M₁ ↠ … ↠ Mₙ ↠ M'`.

The chain always contains at least its final step -- the "zero or more" of Definition 8
refers to the intermediate markings -- so this is the transitive, not the reflexive
transitive, closure of `DirectlyReachable`, and a marking need not be reachable from
itself. Definition 9 depends on that reading; see Section 3.5.1 of the notes. -/
def Reachable (M M' : N.Marking) : Prop :=
  Relation.TransGen DirectlyReachable M M'

/-- `R(M)`, the set of all markings reachable from `M`. -/
def R (M : N.Marking) : Set N.Marking := {M' | Reachable M M'}

variable (N)

/-! ### Reachability graph -/

/-- The states of the reachability graph: `S = {M₀} ∪ R(M₀)`. -/
def RGState : Type _ := {M : N.Marking // M = N.initialMarking ∨ M ∈ R N.initialMarking}

/-- `S` is closed under direct reachability: a marking directly reachable from a state of
the reachability graph is itself a state of the reachability graph. -/
theorem mem_RGState_of_directlyReachable {M M' : N.Marking}
    (hM : M = N.initialMarking ∨ M ∈ R N.initialMarking) (h : DirectlyReachable M M') :
    M' = N.initialMarking ∨ M' ∈ R N.initialMarking :=
  Or.inr <| match hM with
    | Or.inl rfl => Relation.TransGen.single h
    | Or.inr hM => Relation.TransGen.tail hM h

/-- **Definition 9 (Reachability graph of a CPN).**
The reachability graph of a CPN with initial marking `M₀` is the LTS `(S, L, →, s₀)` with
`S = {M₀} ∪ R(M₀)`, `L = T`, `s₀ = M₀`, and a transition `M -t→ M'` whenever some binding
`b ∈ B(t)` makes `(t, b)` occur from `M` to `M'`.

The transition relation is quantified over `S × T × S` here, whereas the thesis writes
`R(M₀) × T × R(M₀)`; see Section 3.5.1 of the notes for why. Restricting to `R(M₀)` would
drop every transition out of `M₀` whenever `M₀ ∉ R(M₀)`, which is the normal case, since
`R` is not reflexive. Here the restriction to `S` is the type `RGState` of the states, and
`mem_RGState_of_directlyReachable` is the completeness half of that argument. -/
def reachabilityGraph : LTS N.RGState T where
  step M t M' := ∃ b : N.TransBinding t, Occurs M.1 b M'.1
  init := ⟨N.initialMarking, Or.inl rfl⟩

end CPN
