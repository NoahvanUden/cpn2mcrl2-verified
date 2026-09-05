/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Bridge.Lang

/-!
# A validated `Net` is a `CPN`

`Cpn2mCrl2/Net.lean` holds Definition 5 as data a file can carry; `Proof/ColoredPetriNets.lean`
holds it as a structure over Lean *types*. This file turns the first into the second.

`Implementation/docs/Plan.md` §3 predicts exactly what has to happen here:

> The Definition 5 side conditions stop being decorative.

They do. `Net.Valid.placesNodup` is what makes `C(p)` a function; `Net.Valid.inArcPlace` is
what gives `E(p,t)` the type `C(p)_MS`; `Net.Valid.varsNodup` is what makes `Type[.]` a
function; `finiteColors` and `finiteV` are the finiteness of two lists. Every field of
`Net.Valid` is consumed below.

## Implementation notes

**Places and transitions are indices.** `Proof/` needs `Finite P` and `Finite T`, so `P` and
`T` are `Fin` of the list lengths rather than the declarations themselves -- a list of
declarations has no `DecidableEq` (it contains expressions) and so no easy `Finite`.
`Net.placeAt` and `Net.transAt` read the declaration back.

**An arc is found rather than chosen.** Definition 5 gives `E` on `A` only, so `Ein` takes the
membership proof. Membership here is `(N.inArc? p t).isSome`, which lets `Option.get` produce
the arc from the proof directly -- no choice principle, and `Ein` depends on the proof only
through proof irrelevance.

## Main definitions

* `Cpn2mCrl2.Net.toCPN` : Definition 5, as `Proof/` states it.
-/

namespace Cpn2mCrl2

namespace Bridge

/-- Reading an arc expression at another color leaves its free variables where they were, so
scoping survives. The mismatched case is the empty bag, which has none. -/
theorem scopedIn_exprAt {Γ : Ctx} {a : ArcDecl} (hs : Expr.ScopedIn Γ a.expr) (c : Color) :
    Expr.ScopedIn Γ (a.exprAt c) := by
  by_cases hc : a.color = c
  · intro p hp
    rw [ArcDecl.freeVars_exprAt hc] at hp
    exact hs p hp
  · have he : a.exprAt c = Expr.emptyBag c := by simp [ArcDecl.exprAt, hc]
    intro p hp
    rw [he] at hp
    cases hp

end Bridge

namespace Net

/-! ## Places and transitions as indices -/

/-- The places of the net, as a finite type. -/
abbrev PIdx (N : Net) : Type := Fin N.places.length

/-- The transitions of the net, as a finite type. -/
abbrev TIdx (N : Net) : Type := Fin N.transitions.length

/-- The declaration of a place. -/
def placeAt (N : Net) (p : N.PIdx) : PlaceDecl := N.places[p.1]'p.2

/-- The declaration of a transition. -/
def transAt (N : Net) (t : N.TIdx) : TransDecl := N.transitions[t.1]'t.2

theorem placeAt_mem (N : Net) (p : N.PIdx) : N.placeAt p ∈ N.places := List.getElem_mem _

theorem transAt_mem (N : Net) (t : N.TIdx) : N.transAt t ∈ N.transitions := List.getElem_mem _

theorem exists_placeAt {N : Net} {n : String} (hn : n ∈ N.placeNames) :
    ∃ p : N.PIdx, (N.placeAt p).name = n := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hn
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hd
  exact ⟨⟨i, hi⟩, by rw [placeAt, hget]⟩

theorem exists_transAt {N : Net} {n : String} (hn : n ∈ N.transNames) :
    ∃ t : N.TIdx, (N.transAt t).name = n := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hn
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hd
  exact ⟨⟨i, hi⟩, by rw [transAt, hget]⟩

/-! ## The arc sets -/

/-- The arcs of `A` in `P × T`, as a set of index pairs. -/
def cpnInArc (N : Net) : Set (N.PIdx × N.TIdx) :=
  {a | (N.inArc? (N.placeAt a.1).name (N.transAt a.2).name).isSome = true}

/-- The arcs of `A` in `T × P`, as a set of index pairs. -/
def cpnOutArc (N : Net) : Set (N.TIdx × N.PIdx) :=
  {a | (N.outArc? (N.transAt a.1).name (N.placeAt a.2).name).isSome = true}

/-- The arc an index pair of `cpnInArc` names. -/
def arcOfIn (N : Net) (a : N.PIdx × N.TIdx) (ha : a ∈ N.cpnInArc) : ArcDecl :=
  (N.inArc? (N.placeAt a.1).name (N.transAt a.2).name).get ha

/-- The arc an index pair of `cpnOutArc` names. -/
def arcOfOut (N : Net) (a : N.TIdx × N.PIdx) (ha : a ∈ N.cpnOutArc) : ArcDecl :=
  (N.outArc? (N.transAt a.1).name (N.placeAt a.2).name).get ha

theorem inArc?_arcOfIn (N : Net) (a : N.PIdx × N.TIdx) (ha : a ∈ N.cpnInArc) :
    N.inArc? (N.placeAt a.1).name (N.transAt a.2).name = some (N.arcOfIn a ha) :=
  (Option.some_get ha).symm

theorem outArc?_arcOfOut (N : Net) (a : N.TIdx × N.PIdx) (ha : a ∈ N.cpnOutArc) :
    N.outArc? (N.transAt a.1).name (N.placeAt a.2).name = some (N.arcOfOut a ha) :=
  (Option.some_get ha).symm

theorem arcOfIn_mem (N : Net) (a : N.PIdx × N.TIdx) (ha : a ∈ N.cpnInArc) :
    N.arcOfIn a ha ∈ N.inArcs :=
  List.mem_of_find?_eq_some (N.inArc?_arcOfIn a ha)

theorem arcOfOut_mem (N : Net) (a : N.TIdx × N.PIdx) (ha : a ∈ N.cpnOutArc) :
    N.arcOfOut a ha ∈ N.outArcs :=
  List.mem_of_find?_eq_some (N.outArc?_arcOfOut a ha)

theorem arcOfIn_names (N : Net) (a : N.PIdx × N.TIdx) (ha : a ∈ N.cpnInArc) :
    (N.arcOfIn a ha).place = (N.placeAt a.1).name ∧
      (N.arcOfIn a ha).transition = (N.transAt a.2).name := by
  have hp := List.find?_some (N.inArc?_arcOfIn a ha)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact hp

theorem arcOfOut_names (N : Net) (a : N.TIdx × N.PIdx) (ha : a ∈ N.cpnOutArc) :
    (N.arcOfOut a ha).place = (N.placeAt a.2).name ∧
      (N.arcOfOut a ha).transition = (N.transAt a.1).name := by
  have hp := List.find?_some (N.outArc?_arcOfOut a ha)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact hp

theorem arcOfIn_color {N : Net} (h : N.Valid) (a : N.PIdx × N.TIdx) (ha : a ∈ N.cpnInArc) :
    (N.arcOfIn a ha).color = (N.placeAt a.1).color := by
  have h1 := h.inArcPlace _ (N.arcOfIn_mem a ha)
  rw [(N.arcOfIn_names a ha).1] at h1
  exact Option.some.inj (h1.symm.trans (placeColor?_of_mem h (N.placeAt_mem a.1)))

theorem arcOfOut_color {N : Net} (h : N.Valid) (a : N.TIdx × N.PIdx) (ha : a ∈ N.cpnOutArc) :
    (N.arcOfOut a ha).color = (N.placeAt a.2).color := by
  have h1 := h.outArcPlace _ (N.arcOfOut_mem a ha)
  rw [(N.arcOfOut_names a ha).1] at h1
  exact Option.some.inj (h1.symm.trans (placeColor?_of_mem h (N.placeAt_mem a.2)))

/-! ## The CPN -/

/-- `V`, as `Proof/` wants it: a set of variable names. -/
def cpnV (N : Net) : Set String := {x | x ∈ N.varNames}

/-- `Σ`, as a set. -/
def cpnColors (N : Net) : Set Color := {c | c ∈ N.colors}

theorem varTypeOf_mem_colors {N : Net} (h : N.Valid) {x : String} (hx : x ∈ N.cpnV) :
    N.varTypeOf x ∈ N.cpnColors := by
  obtain ⟨⟨y, σ⟩, hq, rfl⟩ := List.mem_map.1 hx
  have hσ := Net.varTypeOf_of_mem h hq
  have hc := h.varTypeMem _ hq
  rw [hσ] at hc
  exact hc

/-- The guard of a transition, as an expression of the language. -/
def cpnG (N : Net) (h : N.Valid) (t : N.TIdx) :
    (N.lang h).ExprOn N.cpnV (.color (N.lang h).boolColor) :=
  ⟨⟨(N.transAt t).guard, h.guardScoped _ (N.transAt_mem t)⟩, N.langVars_subset_varNames _⟩

/-- `E(p, t)`, as an expression of the language of the place's own bag sort. -/
def cpnEin (N : Net) (h : N.Valid) (a : N.PIdx × N.TIdx) (ha : a ∈ N.cpnInArc) :
    (N.lang h).ExprOn N.cpnV (.bag (N.placeAt a.1).color) :=
  ⟨⟨(N.arcOfIn a ha).exprAt (N.placeAt a.1).color,
      Bridge.scopedIn_exprAt (h.inArcScoped _ (N.arcOfIn_mem a ha)) _⟩,
    N.langVars_subset_varNames _⟩

/-- `E(t, p)`. -/
def cpnEout (N : Net) (h : N.Valid) (a : N.TIdx × N.PIdx) (ha : a ∈ N.cpnOutArc) :
    (N.lang h).ExprOn N.cpnV (.bag (N.placeAt a.2).color) :=
  ⟨⟨(N.arcOfOut a ha).exprAt (N.placeAt a.2).color,
      Bridge.scopedIn_exprAt (h.outArcScoped _ (N.arcOfOut_mem a ha)) _⟩,
    N.langVars_subset_varNames _⟩

theorem initScoped {N : Net} (h : N.Valid) (p : N.PIdx) :
    Expr.ScopedIn N.vars (N.placeAt p).init := by
  intro q hq
  rw [h.initClosed _ (N.placeAt_mem p)] at hq
  cases hq

theorem initLangVars {N : Net} (h : N.Valid) (p : N.PIdx) :
    N.langVars (τ := .bag (N.placeAt p).color) ⟨(N.placeAt p).init, initScoped h p⟩ ⊆ ∅ := by
  rintro x ⟨σ, hσ⟩
  have hf : (x, σ) ∈ (N.placeAt p).init.freeVars := hσ
  rw [h.initClosed _ (N.placeAt_mem p)] at hf
  cases hf

/-- `I(p)`, a closed expression. -/
def cpnI (N : Net) (h : N.Valid) (p : N.PIdx) :
    (N.lang h).ExprOn ∅ (.bag (N.placeAt p).color) :=
  ⟨⟨(N.placeAt p).init, initScoped h p⟩, initLangVars h p⟩

/-- **Definition 5, as `Proof/` states it.**
The CPN a validated `Net` denotes: places and transitions are indices into the two lists, the
arc sets are the pairs whose lookup succeeds, and `C`, `G`, `E` and `I` read the declarations
back. -/
noncomputable def toCPN (N : Net) (h : N.Valid) : CPN (N.lang h) N.PIdx N.TIdx where
  finitePlaces := inferInstance
  finiteTransitions := inferInstance
  inArc := N.cpnInArc
  outArc := N.cpnOutArc
  colors := N.cpnColors
  finiteColors := N.colors.finite_toSet
  boolMem := h.boolMem
  V := N.cpnV
  finiteV := N.varNames.finite_toSet
  varTypeMem := fun _ hv => varTypeOf_mem_colors h hv
  C := fun p => (N.placeAt p).color
  colorMem := fun p => h.colorMem _ (N.placeAt_mem p)
  G := N.cpnG h
  Ein := N.cpnEin h
  Eout := N.cpnEout h
  I := N.cpnI h

@[simp] theorem toCPN_C (N : Net) (h : N.Valid) (p : N.PIdx) :
    (N.toCPN h).C p = (N.placeAt p).color := rfl

@[simp] theorem toCPN_inArc (N : Net) (h : N.Valid) : (N.toCPN h).inArc = N.cpnInArc := rfl

@[simp] theorem toCPN_outArc (N : Net) (h : N.Valid) : (N.toCPN h).outArc = N.cpnOutArc := rfl

@[simp] theorem toCPN_G (N : Net) (h : N.Valid) (t : N.TIdx) :
    ((N.toCPN h).G t).1.1 = (N.transAt t).guard := rfl

@[simp] theorem toCPN_Ein (N : Net) (h : N.Valid) (a : N.PIdx × N.TIdx) (ha : a ∈ N.cpnInArc) :
    ((N.toCPN h).Ein a ha).1.1 = (N.arcOfIn a ha).exprAt (N.placeAt a.1).color := rfl

@[simp] theorem toCPN_Eout (N : Net) (h : N.Valid) (a : N.TIdx × N.PIdx)
    (ha : a ∈ N.cpnOutArc) :
    ((N.toCPN h).Eout a ha).1.1 = (N.arcOfOut a ha).exprAt (N.placeAt a.2).color := rfl

@[simp] theorem toCPN_I (N : Net) (h : N.Valid) (p : N.PIdx) :
    ((N.toCPN h).I p).1.1 = (N.placeAt p).init := rfl

end Net

end Cpn2mCrl2
