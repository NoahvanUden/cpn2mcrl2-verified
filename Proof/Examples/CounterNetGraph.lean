/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Examples.CounterNet

/-!
# Example 5: the reachability graph of the counter net

The reachability graph (Definition 9) of the CPN of Example 3 of the thesis *Model checking
for analysis of BPMN models* (N. van Uden, TU/e, 2025), Chapter 3.

See `Thesis/docs/ColoredPetriNets.md` for the prose version. Example 5 of those notes records
a **deviation from the thesis**: Figure 3.4 draws this graph as the eight-state chain
`T₁ T₂ T₁ T₂ T₁ T₂ T₃`, and the notes correct it to the seven-state chain

    M₀ -T₁→ M₁ -T₂→ M₂ -T₁→ M₃ -T₂→ M₄ -T₁→ M₅ -T₃→ M₆

because after the third `T₁` the token in `p₂` has value 4, which violates the guard `n ≤ 3`
of `T₂`. That correction is `not_enabled_t₂_M₅` below; the chain is `occurs_M₀_M₁` through
`occurs_M₅_M₆`, and that these are the *only* steps is `directlyReachable_M₀` through
`not_directlyReachable_M₆`.

Section 3.5.1 of the notes argues that the transition relation of Definition 9 has to range
over `S = {M₀} ∪ R(M₀)` rather than over `R(M₀)`, on the grounds that `R` is not reflexive and
`M₀ ∉ R(M₀)` for this very net. That is `not_mem_R_initialMarking`, and `step_init` is the
`t₁` transition out of the initial state that the restriction to `R(M₀)` would drop.

## Main results

* `occurs_M₀_M₁` … `occurs_M₅_M₆` : the six steps of the chain, with their bindings.
* `not_enabled_t₂_M₅` : the correction — the extra `T₂` step of Figure 3.4 cannot occur.
* `directlyReachable_M₀` … `not_directlyReachable_M₆` : these are the only steps.
* `reachable_M₀_iff` : `R(M₀)` is exactly `{M₁, …, M₆}`.
* `rgStates_eq`, `states_injective` : the reachability graph has exactly seven states.
* `not_mem_R_initialMarking` : `M₀ ∉ R(M₀)`, as Section 3.5.1 claims.
-/

namespace CounterNet

open scoped LTS

/-! ## Bag facts

The bags occurring in this net are all either empty or a single token, so the whole
computation rests on the following. -/

section BagLemmas

variable {S : Type*}

@[simp] theorem empty_union (m : Bag S) : (∅ : Bag S) ∪ m = m := by ext s; simp

@[simp] theorem union_empty (m : Bag S) : m ∪ (∅ : Bag S) = m := by ext s; simp

@[simp] theorem empty_sdiff (m : Bag S) : (∅ : Bag S) \ m = ∅ := by ext s; simp

@[simp] theorem sdiff_empty (m : Bag S) : m \ (∅ : Bag S) = m := by ext s; simp

variable [DecidableEq S]

@[simp] theorem single_self (a : S) : (Bag.single 1 a : Bag S) a = 1 := by simp

theorem single_apply_of_ne {a b : S} (h : a ≠ b) : (Bag.single 1 b : Bag S) a = 0 := by
  simp [h]

@[simp] theorem single_sdiff_self (a : S) :
    (Bag.single 1 a \ Bag.single 1 a : Bag S) = ∅ := by
  ext s; simp

/-- A single token is a sub-bag of a single token exactly when they carry the same value. -/
theorem single_subset_single_iff {a b : S} :
    (Bag.single 1 a : Bag S) ⊆ Bag.single 1 b ↔ a = b := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hne
    have h1 := h a
    rw [single_self, single_apply_of_ne hne] at h1
    omega
  · rintro rfl
    exact fun _ => le_refl _

/-- A place holding no tokens cannot supply one. -/
theorem not_single_subset_empty (a : S) : ¬ (Bag.single 1 a : Bag S) ⊆ ∅ := by
  intro h
  have h1 := h a
  rw [single_self, Bag.empty_apply] at h1
  omega

theorem single_ne_empty (a : S) : (Bag.single 1 a : Bag S) ≠ ∅ := by
  intro h
  have h1 : (Bag.single 1 a : Bag S) a = (∅ : Bag S) a := by rw [h]
  rw [single_self, Bag.empty_apply] at h1
  omega

theorem single_ne_single {a b : S} (hab : a ≠ b) :
    (Bag.single 1 a : Bag S) ≠ Bag.single 1 b := by
  intro h
  have h1 : (Bag.single 1 a : Bag S) a = (Bag.single 1 b : Bag S) a := by rw [h]
  rw [single_self, single_apply_of_ne hab] at h1
  omega

end BagLemmas

/-! ## Markings differ place by place -/

theorem marking_ne_of_p₁ {a b c a' b' c' : Bag ℤ} (h : a ≠ a') :
    marking a b c ≠ marking a' b' c' := fun he => h (congrFun he Place.p₁)

theorem marking_ne_of_p₂ {a b c a' b' c' : Bag ℤ} (h : b ≠ b') :
    marking a b c ≠ marking a' b' c' := fun he => h (congrFun he Place.p₂)

theorem marking_ne_of_p₃ {a b c a' b' c' : Bag ℤ} (h : c ≠ c') :
    marking a b c ≠ marking a' b' c' := fun he => h (congrFun he Place.p₃)

/-! ## The seven markings

Following the text of Example 5: `p₁` starts with the token `{1`1}`; `t₁` moves it to `p₂`
incremented by one; `t₂` moves it back to `p₁` while its value is at most three; once the
value is four, `t₃` moves it to `p₃`. -/

/-- `M₀ = ({1`1}, ∅, ∅)`, the initial marking. -/
def M₀ : net.Marking := marking (Bag.single 1 (1 : ℤ)) ∅ ∅

/-- `M₁ = (∅, {1`2}, ∅)`, after `T₁`. -/
def M₁ : net.Marking := marking ∅ (Bag.single 1 (2 : ℤ)) ∅

/-- `M₂ = ({1`2}, ∅, ∅)`, after `T₂`. -/
def M₂ : net.Marking := marking (Bag.single 1 (2 : ℤ)) ∅ ∅

/-- `M₃ = (∅, {1`3}, ∅)`, after `T₁`. -/
def M₃ : net.Marking := marking ∅ (Bag.single 1 (3 : ℤ)) ∅

/-- `M₄ = ({1`3}, ∅, ∅)`, after `T₂`. -/
def M₄ : net.Marking := marking (Bag.single 1 (3 : ℤ)) ∅ ∅

/-- `M₅ = (∅, {1`4}, ∅)`, after `T₁`. This is where Figure 3.4 draws a further `T₂` step. -/
def M₅ : net.Marking := marking ∅ (Bag.single 1 (4 : ℤ)) ∅

/-- `M₆ = (∅, ∅, {1`4})`, after `T₃`. -/
def M₆ : net.Marking := marking ∅ ∅ (Bag.single 1 (4 : ℤ))

theorem initialMarking_eq_M₀ : net.initialMarking = M₀ := initialMarking_eq

/-- The binding `⟨n = v⟩` of a transition `t`. -/
def bind (t : Trans) (v : ℤ) : net.TransBinding t := fun x =>
  match x.1 with
  | .n => v

@[simp] theorem valueOf_bind (t : Trans) (v : ℤ) : valueOf (bind t v) = v := rfl

/-! ## The steps of the chain

Each transition is stated for an arbitrary marking first, then specialized. -/

theorem occurs_t₁ (a b c : Bag ℤ) (v : ℤ) (h : Bag.single 1 v ⊆ a) :
    CPN.Occurs (marking a b c) (bind .t₁ v)
      (marking (a \ Bag.single 1 v) (b ∪ Bag.single 1 (v + 1)) c) :=
  ⟨(enabled_t₁_iff _ _).2 (by simpa using h), by rw [fire_t₁]; simp⟩

theorem occurs_t₂ (a b c : Bag ℤ) (v : ℤ) (h : Bag.single 1 v ⊆ b) (hv : v ≤ 3) :
    CPN.Occurs (marking a b c) (bind .t₂ v)
      (marking (a ∪ Bag.single 1 v) (b \ Bag.single 1 v) c) :=
  ⟨(enabled_t₂_iff _ _).2 ⟨by simpa using h, by simpa using hv⟩, by rw [fire_t₂]; simp⟩

theorem occurs_t₃ (a b c : Bag ℤ) (v : ℤ) (h : Bag.single 1 v ⊆ b) (hv : 3 < v) :
    CPN.Occurs (marking a b c) (bind .t₃ v)
      (marking a (b \ Bag.single 1 v) (c ∪ Bag.single 1 v)) :=
  ⟨(enabled_t₃_iff _ _).2 ⟨by simpa using h, by simpa using hv⟩, by rw [fire_t₃]; simp⟩

/-- `M₀ -T₁→ M₁` with the binding `⟨n = 1⟩`, which is the occurrence computed in Example 4. -/
theorem occurs_M₀_M₁ : CPN.Occurs M₀ (bind .t₁ 1) M₁ := by
  have h := occurs_t₁ (Bag.single 1 (1 : ℤ)) ∅ ∅ 1 (fun _ => le_refl _)
  simpa [M₀, M₁, show (1 : ℤ) + 1 = 2 by norm_num] using h

/-- `M₁ -T₂→ M₂` with the binding `⟨n = 2⟩`; the guard `n ≤ 3` holds. -/
theorem occurs_M₁_M₂ : CPN.Occurs M₁ (bind .t₂ 2) M₂ := by
  have h := occurs_t₂ ∅ (Bag.single 1 (2 : ℤ)) ∅ 2 (fun _ => le_refl _) (by norm_num)
  simpa [M₁, M₂] using h

/-- `M₂ -T₁→ M₃` with the binding `⟨n = 2⟩`. -/
theorem occurs_M₂_M₃ : CPN.Occurs M₂ (bind .t₁ 2) M₃ := by
  have h := occurs_t₁ (Bag.single 1 (2 : ℤ)) ∅ ∅ 2 (fun _ => le_refl _)
  simpa [M₂, M₃, show (2 : ℤ) + 1 = 3 by norm_num] using h

/-- `M₃ -T₂→ M₄` with the binding `⟨n = 3⟩`; the guard `n ≤ 3` still holds, just. -/
theorem occurs_M₃_M₄ : CPN.Occurs M₃ (bind .t₂ 3) M₄ := by
  have h := occurs_t₂ ∅ (Bag.single 1 (3 : ℤ)) ∅ 3 (fun _ => le_refl _) (by norm_num)
  simpa [M₃, M₄] using h

/-- `M₄ -T₁→ M₅` with the binding `⟨n = 3⟩`. The token in `p₂` now has value 4. -/
theorem occurs_M₄_M₅ : CPN.Occurs M₄ (bind .t₁ 3) M₅ := by
  have h := occurs_t₁ (Bag.single 1 (3 : ℤ)) ∅ ∅ 3 (fun _ => le_refl _)
  simpa [M₄, M₅, show (3 : ℤ) + 1 = 4 by norm_num] using h

/-- `M₅ -T₃→ M₆` with the binding `⟨n = 4⟩`; the guard `n > 3` holds. -/
theorem occurs_M₅_M₆ : CPN.Occurs M₅ (bind .t₃ 4) M₆ := by
  have h := occurs_t₃ ∅ (Bag.single 1 (4 : ℤ)) ∅ 4 (fun _ => le_refl _) (by norm_num)
  simpa [M₅, M₆] using h

/-! ## The correction to Figure 3.4 -/

/-- **The extra `T₂` step of Figure 3.4 cannot occur.** In `M₅` the token in `p₂` carries the
value 4, so any binding of `t₂` that takes a token from `p₂` binds `n` to 4 — and then the
guard `G(t₂) = n ≤ 3` fails. No binding of `t₂` is enabled in `M₅`. -/
theorem not_enabled_t₂_M₅ (b : net.TransBinding .t₂) : ¬ CPN.Enabled M₅ b := by
  rw [enabled_t₂_iff]
  rintro ⟨hsub, hle⟩
  rw [M₅, marking_p₂] at hsub
  rw [single_subset_single_iff.1 hsub] at hle
  norm_num at hle

/-! ## These are the only steps

The three shapes of marking this net ever has: a token in `p₁`, a token in `p₂`, or a token
in `p₃` and nothing else. -/

/-- From `({1`v}, ∅, ∅)` only `t₁` can occur, and only with `n` bound to `v`: `t₂` and `t₃`
both take their token from `p₂`, which is empty. -/
theorem directlyReachable_left (v : ℤ) (M : net.Marking) :
    CPN.DirectlyReachable (marking (Bag.single 1 v) ∅ ∅) M
      ↔ M = marking ∅ (Bag.single 1 (v + 1)) ∅ := by
  constructor
  · rintro ⟨t, b, hen, rfl⟩
    cases t
    · rw [enabled_t₁_iff, marking_p₁] at hen
      rw [fire_t₁]
      simp [single_subset_single_iff.1 hen]
    · rw [enabled_t₂_iff, marking_p₂] at hen
      exact absurd hen.1 (not_single_subset_empty _)
    · rw [enabled_t₃_iff, marking_p₂] at hen
      exact absurd hen.1 (not_single_subset_empty _)
  · rintro rfl
    exact ⟨.t₁, bind .t₁ v, by simpa using occurs_t₁ (Bag.single 1 v) ∅ ∅ v (fun _ => le_refl _)⟩

/-- From `(∅, {1`v}, ∅)` with `v ≤ 3` only `t₂` can occur: `t₁` takes its token from `p₁`,
which is empty, and the guard of `t₃` fails. -/
theorem directlyReachable_mid_le {v : ℤ} (hv : v ≤ 3) (M : net.Marking) :
    CPN.DirectlyReachable (marking ∅ (Bag.single 1 v) ∅) M
      ↔ M = marking (Bag.single 1 v) ∅ ∅ := by
  constructor
  · rintro ⟨t, b, hen, rfl⟩
    cases t
    · rw [enabled_t₁_iff, marking_p₁] at hen
      exact absurd hen (not_single_subset_empty _)
    · rw [enabled_t₂_iff, marking_p₂] at hen
      rw [fire_t₂]
      simp [single_subset_single_iff.1 hen.1]
    · rw [enabled_t₃_iff, marking_p₂] at hen
      rw [single_subset_single_iff.1 hen.1] at hen
      omega
  · rintro rfl
    exact ⟨.t₂, bind .t₂ v,
      by simpa using occurs_t₂ ∅ (Bag.single 1 v) ∅ v (fun _ => le_refl _) hv⟩

/-- From `(∅, {1`v}, ∅)` with `v > 3` only `t₃` can occur: the guard of `t₂` now fails. This
is the step that Figure 3.4 gets wrong for `v = 4`. -/
theorem directlyReachable_mid_gt {v : ℤ} (hv : 3 < v) (M : net.Marking) :
    CPN.DirectlyReachable (marking ∅ (Bag.single 1 v) ∅) M
      ↔ M = marking ∅ ∅ (Bag.single 1 v) := by
  constructor
  · rintro ⟨t, b, hen, rfl⟩
    cases t
    · rw [enabled_t₁_iff, marking_p₁] at hen
      exact absurd hen (not_single_subset_empty _)
    · rw [enabled_t₂_iff, marking_p₂] at hen
      rw [single_subset_single_iff.1 hen.1] at hen
      omega
    · rw [enabled_t₃_iff, marking_p₂] at hen
      rw [fire_t₃]
      simp [single_subset_single_iff.1 hen.1]
  · rintro rfl
    exact ⟨.t₃, bind .t₃ v,
      by simpa using occurs_t₃ ∅ (Bag.single 1 v) ∅ v (fun _ => le_refl _) hv⟩

/-- A marking that holds tokens only in `p₃` is a deadlock: every transition of this net
consumes a token from `p₁` or from `p₂`. -/
theorem not_directlyReachable_right (c : Bag ℤ) (M : net.Marking) :
    ¬ CPN.DirectlyReachable (marking ∅ ∅ c) M := by
  rintro ⟨t, b, hen, -⟩
  cases t
  · rw [enabled_t₁_iff, marking_p₁] at hen
    exact absurd hen (not_single_subset_empty _)
  · rw [enabled_t₂_iff, marking_p₂] at hen
    exact absurd hen.1 (not_single_subset_empty _)
  · rw [enabled_t₃_iff, marking_p₂] at hen
    exact absurd hen.1 (not_single_subset_empty _)

theorem directlyReachable_M₀ (M : net.Marking) : CPN.DirectlyReachable M₀ M ↔ M = M₁ := by
  rw [M₀, directlyReachable_left, M₁]; norm_num

theorem directlyReachable_M₁ (M : net.Marking) : CPN.DirectlyReachable M₁ M ↔ M = M₂ := by
  rw [M₁, directlyReachable_mid_le (by norm_num), M₂]

theorem directlyReachable_M₂ (M : net.Marking) : CPN.DirectlyReachable M₂ M ↔ M = M₃ := by
  rw [M₂, directlyReachable_left, M₃]; norm_num

theorem directlyReachable_M₃ (M : net.Marking) : CPN.DirectlyReachable M₃ M ↔ M = M₄ := by
  rw [M₃, directlyReachable_mid_le (by norm_num), M₄]

theorem directlyReachable_M₄ (M : net.Marking) : CPN.DirectlyReachable M₄ M ↔ M = M₅ := by
  rw [M₄, directlyReachable_left, M₅]; norm_num

/-- The step Figure 3.4 gets wrong: from `M₅` the only step is `T₃`, not a further `T₂`. -/
theorem directlyReachable_M₅ (M : net.Marking) : CPN.DirectlyReachable M₅ M ↔ M = M₆ := by
  rw [M₅, directlyReachable_mid_gt (by norm_num), M₆]

/-- `M₆` is a deadlock, so the chain ends there and has seven states. -/
theorem not_directlyReachable_M₆ (M : net.Marking) : ¬ CPN.DirectlyReachable M₆ M :=
  not_directlyReachable_right _ M

/-! ## The reachable markings -/

/-- `R(M₀)`, the markings reachable from the initial marking, is exactly `{M₁, …, M₆}`. Note
that `M₀` is **not** among them: Definition 8 is a transitive, not a reflexive-transitive,
closure, and this net never returns to its initial marking. -/
theorem reachable_M₀_iff (M : net.Marking) :
    CPN.Reachable M₀ M ↔ M = M₁ ∨ M = M₂ ∨ M = M₃ ∨ M = M₄ ∨ M = M₅ ∨ M = M₆ := by
  constructor
  · intro h
    induction h with
    | single hs => exact Or.inl ((directlyReachable_M₀ _).1 hs)
    | tail _ hs ih =>
        rcases ih with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl ((directlyReachable_M₁ _).1 hs))
        · exact Or.inr (Or.inr (Or.inl ((directlyReachable_M₂ _).1 hs)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ((directlyReachable_M₃ _).1 hs))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((directlyReachable_M₄ _).1 hs)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((directlyReachable_M₅ _).1 hs)))))
        · exact absurd hs (not_directlyReachable_M₆ _)
  · have h₀₁ : CPN.DirectlyReachable M₀ M₁ := ⟨_, _, occurs_M₀_M₁⟩
    have h₁₂ : CPN.DirectlyReachable M₁ M₂ := ⟨_, _, occurs_M₁_M₂⟩
    have h₂₃ : CPN.DirectlyReachable M₂ M₃ := ⟨_, _, occurs_M₂_M₃⟩
    have h₃₄ : CPN.DirectlyReachable M₃ M₄ := ⟨_, _, occurs_M₃_M₄⟩
    have h₄₅ : CPN.DirectlyReachable M₄ M₅ := ⟨_, _, occurs_M₄_M₅⟩
    have h₅₆ : CPN.DirectlyReachable M₅ M₆ := ⟨_, _, occurs_M₅_M₆⟩
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .single h₀₁
    · exact (Relation.TransGen.single h₀₁).tail h₁₂
    · exact ((Relation.TransGen.single h₀₁).tail h₁₂).tail h₂₃
    · exact (((Relation.TransGen.single h₀₁).tail h₁₂).tail h₂₃).tail h₃₄
    · exact ((((Relation.TransGen.single h₀₁).tail h₁₂).tail h₂₃).tail h₃₄).tail h₄₅
    · exact (((((Relation.TransGen.single h₀₁).tail h₁₂).tail h₂₃).tail h₃₄).tail h₄₅).tail h₅₆

/-- **`M₀ ∉ R(M₀)`.** This is the claim Section 3.5.1 of the notes rests on: the reachability
relation of Definition 8 is not reflexive, so `{M₀} ∪ R(M₀)` of Definition 9 is a genuine
union, and restricting the transition relation to `R(M₀)` would leave the initial state with
no outgoing transitions at all. -/
theorem not_mem_R_initialMarking : net.initialMarking ∉ CPN.R net.initialMarking := by
  rw [initialMarking_eq_M₀]
  intro h
  have h' := (reachable_M₀_iff M₀).1 h
  rw [M₀, M₁, M₂, M₃, M₄, M₅, M₆] at h'
  rcases h' with h | h | h | h | h | h
  · exact marking_ne_of_p₁ (single_ne_empty (1 : ℤ)) h
  · exact marking_ne_of_p₁ (single_ne_single (show (1 : ℤ) ≠ 2 by norm_num)) h
  · exact marking_ne_of_p₁ (single_ne_empty (1 : ℤ)) h
  · exact marking_ne_of_p₁ (single_ne_single (show (1 : ℤ) ≠ 3 by norm_num)) h
  · exact marking_ne_of_p₁ (single_ne_empty (1 : ℤ)) h
  · exact marking_ne_of_p₁ (single_ne_empty (1 : ℤ)) h

/-! ## Seven states

`S = {M₀} ∪ R(M₀)` is the range of `states`, and `states` is injective, so the reachability
graph has exactly seven states — not the eight of Figure 3.4. -/

/-- The seven states of the reachability graph, in the order they occur along the chain. -/
def states : Fin 7 → net.Marking
  | 0 => M₀
  | 1 => M₁
  | 2 => M₂
  | 3 => M₃
  | 4 => M₄
  | 5 => M₅
  | 6 => M₆

/-- A number read off a marking that recovers the position of each of the seven states along
the chain, used only to tell them apart. -/
def idx (M : net.Marking) : ℕ :=
  1 * M .p₂ (2 : ℤ) + 2 * M .p₁ (2 : ℤ) + 3 * M .p₂ (3 : ℤ)
    + 4 * M .p₁ (3 : ℤ) + 5 * M .p₂ (4 : ℤ) + 6 * M .p₃ (4 : ℤ)

theorem idx_states (i : Fin 7) : idx (states i) = (i : ℕ) := by
  fin_cases i <;>
    norm_num [idx, states, M₀, M₁, M₂, M₃, M₄, M₅, M₆, marking, Bag.single]

/-- The seven markings are pairwise distinct. -/
theorem states_injective : Function.Injective states := fun i j h => by
  have := congrArg idx h
  rw [idx_states, idx_states] at this
  exact Fin.val_injective this

/-- `S = {M₀} ∪ R(M₀)` is exactly the range of `states`: the reachability graph has these
seven states and no others. -/
theorem rgStates_eq :
    {M : net.Marking | M = net.initialMarking ∨ M ∈ CPN.R net.initialMarking}
      = Set.range states := by
  rw [initialMarking_eq_M₀]
  ext M
  simp only [Set.mem_ofPred_eq, CPN.R, Set.mem_ofPred_eq, reachable_M₀_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [states]

/-- Every one of the seven markings is a state of the reachability graph. -/
theorem mem_rgState (i : Fin 7) :
    states i = net.initialMarking ∨ states i ∈ CPN.R net.initialMarking := by
  have h : states i ∈ Set.range states := Set.mem_range_self i
  rw [← rgStates_eq] at h
  exact h

/-! ## The chain as an LTS

The same six steps, now as transitions of `net.reachabilityGraph` (Definition 9). -/

/-- The seven states of the reachability graph as elements of its state type. -/
def rg (i : Fin 7) : net.RGState := ⟨states i, mem_rgState i⟩

theorem rg_zero : rg 0 = net.reachabilityGraph.init :=
  Subtype.ext initialMarking_eq_M₀.symm

theorem rg_step_M₀ : net.reachabilityGraph ⊢ rg 0 -[.t₁]→ rg 1 := ⟨_, occurs_M₀_M₁⟩

theorem rg_step_M₁ : net.reachabilityGraph ⊢ rg 1 -[.t₂]→ rg 2 := ⟨_, occurs_M₁_M₂⟩

theorem rg_step_M₂ : net.reachabilityGraph ⊢ rg 2 -[.t₁]→ rg 3 := ⟨_, occurs_M₂_M₃⟩

theorem rg_step_M₃ : net.reachabilityGraph ⊢ rg 3 -[.t₂]→ rg 4 := ⟨_, occurs_M₃_M₄⟩

theorem rg_step_M₄ : net.reachabilityGraph ⊢ rg 4 -[.t₁]→ rg 5 := ⟨_, occurs_M₄_M₅⟩

/-- The last step is `T₃`, not the `T₂` of Figure 3.4. -/
theorem rg_step_M₅ : net.reachabilityGraph ⊢ rg 5 -[.t₃]→ rg 6 := ⟨_, occurs_M₅_M₆⟩

/-- The initial state is not isolated. Together with `not_mem_R_initialMarking` this is the
argument of Section 3.5.1: `M₀ ∉ R(M₀)`, so quantifying the transition relation of
Definition 9 over `R(M₀) × T × R(M₀)`, as the thesis prints it, would drop this transition. -/
theorem step_init : net.reachabilityGraph ⊢ net.reachabilityGraph.init -[.t₁]→ rg 1 :=
  rg_zero ▸ rg_step_M₀

/-- Every state of the reachability graph is reachable from the initial state in the sense of
`LTS.Reachable`, so the subtype `RGState` of Definition 9 is neither too big nor too small. -/
theorem rg_reachable : ∀ i : Fin 7, net.reachabilityGraph.Reachable (rg i) := by
  intro i
  have h := net.reachabilityGraph.reachable_init
  rw [← rg_zero] at h
  fin_cases i
  · exact h
  · exact h.step rg_step_M₀
  · exact (h.step rg_step_M₀).step rg_step_M₁
  · exact ((h.step rg_step_M₀).step rg_step_M₁).step rg_step_M₂
  · exact (((h.step rg_step_M₀).step rg_step_M₁).step rg_step_M₂).step rg_step_M₃
  · exact ((((h.step rg_step_M₀).step rg_step_M₁).step rg_step_M₂).step rg_step_M₃).step
      rg_step_M₄
  · exact (((((h.step rg_step_M₀).step rg_step_M₁).step rg_step_M₂).step rg_step_M₃).step
      rg_step_M₄).step rg_step_M₅

end CounterNet
