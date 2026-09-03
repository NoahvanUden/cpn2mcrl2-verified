/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Examples.CounterNet
import Proof.MCRL2

/-!
# Example 9: the LPE of the counter net

The LPE that Definition 14 produces from the CPN of Example 3, checked against the one
printed in Example 9 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025):

    Spec((s_p₁, s_p₂, s_p₃) : (Int_MS × Int_MS × Int_MS)) =
        ∑_{h : Int} ({1`h} ⊆ s_p₁)             → t₁ · Spec(s_p₁ \ {1`h}, s_p₂ ∪ {1`(h+1)}, s_p₃)
      + ∑_{h : Int} ({1`h} ⊆ s_p₂ ∧ h ≤ 3)     → t₂ · Spec(s_p₁ ∪ {1`h}, s_p₂ \ {1`h}, s_p₃)
      + ∑_{h : Int} ({1`h} ⊆ s_p₂ ∧ h > 3)     → t₃ · Spec(s_p₁, s_p₂ \ {1`h}, s_p₃ ∪ {1`h})

with `d₀ = ({1`1}, ∅, ∅)`.

The three `cond` theorems below are the three summand conditions, and the `next` theorems
are the components of `g_{t₁}`; `g_{t₂}` and `g_{t₃}` go the same way. The `h` of the
summand is `valueOf b`, the integer the binding gives to the only variable of the net.

The condition of the third summand is where `Thesis/docs/mCRL2.md` records a deviation: the
thesis prints `{1`h} ⊆ s_p₃`, and `cond_t₃` below confirms that the translation gives
`s_p₂`, since `pre(t₃) = {p₂}`.
-/

namespace CounterNet

/-! ### The state and the initial state -/

/-- `D` is the tuple with one bag of integers per place, `(Int_MS × Int_MS × Int_MS)`. -/
example : net.toLPE.D = ((p : Place) → Bag ℤ) := rfl

/-- `d₀ = ({1`1}, ∅, ∅)`. -/
theorem toLPEInit_p₁ : net.toLPEInit .p₁ = Bag.single 1 (1 : ℤ) := rfl

theorem toLPEInit_p₂ : net.toLPEInit .p₂ = ∅ := rfl

theorem toLPEInit_p₃ : net.toLPEInit .p₃ = ∅ := rfl

/-! ### The conditions of the three summands

`net.toLPE.cond t d b` is `CPN.Enabled d b` by definition (`CPN.toLPE_cond`), so each of these
is the matching enabledness lemma of `Examples/CounterNet.lean`. -/

/-- `c_{t₁}(d, h) = {1`h} ⊆ s_p₁`. The guard of `t₁` is `True`, and `pre(t₁) = {p₁}`. -/
theorem cond_t₁ (d : net.Marking) (b : net.TransBinding .t₁) :
    net.toLPE.cond .t₁ d b ↔ Bag.single 1 (valueOf b) ⊆ d .p₁ :=
  enabled_t₁_iff d b

/-- `c_{t₂}(d, h) = {1`h} ⊆ s_p₂ ∧ h ≤ 3`. -/
theorem cond_t₂ (d : net.Marking) (b : net.TransBinding .t₂) :
    net.toLPE.cond .t₂ d b ↔ Bag.single 1 (valueOf b) ⊆ d .p₂ ∧ valueOf b ≤ 3 :=
  enabled_t₂_iff d b

/-- `c_{t₃}(d, h) = {1`h} ⊆ s_p₂ ∧ h > 3`, over `s_p₂` and not `s_p₃`. -/
theorem cond_t₃ (d : net.Marking) (b : net.TransBinding .t₃) :
    net.toLPE.cond .t₃ d b ↔ Bag.single 1 (valueOf b) ⊆ d .p₂ ∧ 3 < valueOf b :=
  enabled_t₃_iff d b

/-! ### The next state of the first summand

`g_{t₁}(d, h) = (s_p₁ \ {1`h}, s_p₂ ∪ {1`(h+1)}, s_p₃)`. Each component is one place of the
marking `CPN.fire d b` of `Examples/CounterNet.lean`, which `net.toLPE.next` is by definition
(`CPN.toLPE_next`). -/

theorem next_t₁_p₁ (d : net.Marking) (b : net.TransBinding .t₁) :
    net.toLPE.next .t₁ d b .p₁ = d .p₁ \ Bag.single 1 (valueOf b) :=
  congrFun (fire_t₁ d b) .p₁

theorem next_t₁_p₂ (d : net.Marking) (b : net.TransBinding .t₁) :
    net.toLPE.next .t₁ d b .p₂ = d .p₂ ∪ Bag.single 1 (valueOf b + 1) :=
  congrFun (fire_t₁ d b) .p₂

theorem next_t₁_p₃ (d : net.Marking) (b : net.TransBinding .t₁) :
    net.toLPE.next .t₁ d b .p₃ = d .p₃ :=
  congrFun (fire_t₁ d b) .p₃

end CounterNet
