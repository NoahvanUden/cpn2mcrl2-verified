/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Proof.LabeledTransitionSystems

/-!
# Example 2: a coffee and tea machine

The coffee and tea machine of Example 2 of the thesis *Model checking for analysis of BPMN
models* (N. van Uden, TU/e, 2025), Chapter 2, as an `LTS`. Four states `s₀ … s₃` and the
actions *coin*, *coffee*, *tea* and *dispense*. After inserting a coin the machine gives
the choice between coffee and tea, then dispenses it and returns to the initial state.

See `Thesis/docs/LabeledTransitionSystems.md` for the prose version.
-/
namespace CoffeeMachine

open scoped LTS

/-- The four states of the machine of Example 2. -/
inductive State
  | s₀ | s₁ | s₂ | s₃
  deriving DecidableEq, Repr

/-- The four actions of the machine of Example 2. -/
inductive Action
  | coin | coffee | tea | dispense
  deriving DecidableEq, Repr

/-- The five transitions of the machine of Example 2. -/
inductive Step : State → Action → State → Prop
  | coin : Step .s₀ .coin .s₁
  | coffee : Step .s₁ .coffee .s₂
  | tea : Step .s₁ .tea .s₃
  | dispenseCoffee : Step .s₂ .dispense .s₀
  | dispenseTea : Step .s₃ .dispense .s₀

/-- The LTS of Example 2, with initial state `s₀`. -/
def machine : LTS State Action where
  step := Step
  init := .s₀

example : machine ⊢ .s₀ -[.coin]→ .s₁ := Step.coin

/-- Tea is served: `s₀ -coin→ s₁ -tea→ s₃`. -/
example : machine.Reachable .s₃ :=
  (LTS.Reaches.single Step.coin).trans (LTS.Reaches.single Step.tea)

/-- The machine returns to its initial state after dispensing. -/
example : machine.Reachable .s₀ := machine.reachable_init

end CoffeeMachine
