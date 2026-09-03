/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Proof.LabeledTransitionSystems

/-!
# Bisimulation

Definition 16 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025), Section 5.3.

See `Thesis/docs/Bisimiliarity.md` for the prose version.

Definition 17 and Theorem 1 of that section are in `Proof/Soundness.lean`, since they are
about the LTS induced by the mCRL2 Linear Process Equation a CPN is translated into
(Definitions 14 and 15).

## Implementation notes

Definition 16 lets the two LTSs have different action sets `L` and `L'`, but its two
conditions match a step of one against a step of the other *carrying the same action* `a`,
which only makes sense for actions common to both. Here the two LTSs share one action type,
which is the case the thesis uses it in: in Definition 17 both LTSs have the transitions of
the CPN as their actions.

## Main definitions

* `LTS.Bisimulation` : Definition 16, a bisimulation relation between two LTSs.
* `LTS.BisimilarStates` : two states are bisimilar.
* `LTS.Bisimilar` : two LTSs are bisimilar.
-/

universe u v w

namespace LTS

open scoped LTS

variable {S : Type u} {S' : Type v} {S'' : Type w} {L : Type*}

/-- **Definition 16 (Bisimulation).**
A binary relation `R ⊆ S × S'` between the states of two LTSs `A` and `A'` is a
bisimulation relation if and only if, for any two states `s` of `A` and `s'` of `A'` and
any action `a`:

1. if `s -a→ u` and `s R s'`, then there is a state `u'` of `A'` with `s' -a→ u'` and
   `u R u'`, and
2. if `s' -a→ u'` and `s R s'`, then there is a state `u` of `A` with `s -a→ u` and
   `u R u'`. -/
def Bisimulation (A : LTS S L) (A' : LTS S' L) (R : S → S' → Prop) : Prop :=
  (∀ (s : S) (s' : S') (u : S) (a : L), (A ⊢ s -[a]→ u) → R s s' →
      ∃ u' : S', (A' ⊢ s' -[a]→ u') ∧ R u u') ∧
    (∀ (s : S) (s' : S') (u' : S') (a : L), (A' ⊢ s' -[a]→ u') → R s s' →
      ∃ u : S, (A ⊢ s -[a]→ u) ∧ R u u')

/-- Two states `s` and `s'` are bisimilar if and only if there is a bisimulation relation
`R` with `s R s'`. -/
def BisimilarStates (A : LTS S L) (A' : LTS S' L) (s : S) (s' : S') : Prop :=
  ∃ R : S → S' → Prop, Bisimulation A A' R ∧ R s s'

/-- Two LTSs are bisimilar if and only if their initial states are bisimilar. -/
def Bisimilar (A : LTS S L) (A' : LTS S' L) : Prop :=
  BisimilarStates A A' A.init A'.init

/-! ### Consequences of Definition 16

The definition above is all of Definition 16. What follows are the standard facts that make
bisimilarity of states an equivalence; the thesis states none of them, and Theorem 1 uses
none of them, but they are what one reaches for when exhibiting a bisimulation. -/

/-- Equality is a bisimulation on a single LTS. -/
theorem bisimulation_eq (A : LTS S L) : Bisimulation A A (· = ·) := by
  constructor
  · rintro s _ u a h rfl
    exact ⟨u, h, rfl⟩
  · rintro s _ u' a h rfl
    exact ⟨u', h, rfl⟩

/-- The converse of a bisimulation is a bisimulation. -/
theorem Bisimulation.flip {A : LTS S L} {A' : LTS S' L} {R : S → S' → Prop}
    (h : Bisimulation A A' R) : Bisimulation A' A (fun s' s => R s s') :=
  ⟨fun s' s u' a hstep hR => h.2 s s' u' a hstep hR,
    fun s' s u a hstep hR => h.1 s s' u a hstep hR⟩

/-- The composition of two bisimulations is a bisimulation. -/
theorem Bisimulation.comp {A : LTS S L} {A' : LTS S' L} {A'' : LTS S'' L}
    {R : S → S' → Prop} {R' : S' → S'' → Prop} (h : Bisimulation A A' R)
    (h' : Bisimulation A' A'' R') :
    Bisimulation A A'' (fun s s'' => ∃ s' : S', R s s' ∧ R' s' s'') := by
  constructor
  · rintro s s'' u a hstep ⟨s', hR, hR'⟩
    obtain ⟨u', hstep', hRu⟩ := h.1 s s' u a hstep hR
    obtain ⟨u'', hstep'', hRu'⟩ := h'.1 s' s'' u' a hstep' hR'
    exact ⟨u'', hstep'', u', hRu, hRu'⟩
  · rintro s s'' u'' a hstep ⟨s', hR, hR'⟩
    obtain ⟨u', hstep', hRu'⟩ := h'.2 s' s'' u'' a hstep hR'
    obtain ⟨u, hstepu, hRu⟩ := h.2 s s' u' a hstep' hR
    exact ⟨u, hstepu, u', hRu, hRu'⟩

theorem BisimilarStates.refl (A : LTS S L) (s : S) : BisimilarStates A A s s :=
  ⟨(· = ·), bisimulation_eq A, rfl⟩

theorem BisimilarStates.symm {A : LTS S L} {A' : LTS S' L} {s : S} {s' : S'}
    (h : BisimilarStates A A' s s') : BisimilarStates A' A s' s :=
  let ⟨_, hR, hs⟩ := h
  ⟨_, hR.flip, hs⟩

theorem BisimilarStates.trans {A : LTS S L} {A' : LTS S' L} {A'' : LTS S'' L} {s : S}
    {s' : S'} {s'' : S''} (h : BisimilarStates A A' s s')
    (h' : BisimilarStates A' A'' s' s'') : BisimilarStates A A'' s s'' :=
  let ⟨_, hR, hs⟩ := h
  let ⟨_, hR', hs'⟩ := h'
  ⟨_, hR.comp hR', s', hs, hs'⟩

theorem Bisimilar.refl (A : LTS S L) : Bisimilar A A :=
  BisimilarStates.refl A A.init

theorem Bisimilar.symm {A : LTS S L} {A' : LTS S' L} (h : Bisimilar A A') : Bisimilar A' A :=
  BisimilarStates.symm h

theorem Bisimilar.trans {A : LTS S L} {A' : LTS S' L} {A'' : LTS S'' L} (h : Bisimilar A A')
    (h' : Bisimilar A' A'') : Bisimilar A A'' :=
  BisimilarStates.trans h h'

end LTS
