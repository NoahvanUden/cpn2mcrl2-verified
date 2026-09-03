/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Proof.MCRL2

/-!
# Example 10: three mu-calculus formulas

The three formulas of Example 10 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025), over an LTS with actions `L = {a, b, c}` and fixpoint variables
`Var = {X}`.

The thesis writes *true* in place of a set of actions to mean the complete set `L`; that is
`allActions` here, since the shorthands of Section 2.2 need the actions as a list.

These are terms of the grammar of Definition 18 and nothing more: the thesis gives the
syntax of the logic and the meaning of each formula in words, but no semantics over an LTS,
so there is nothing to prove about them here. The `rfl` theorems below only unfold the
shorthand notation into the grammar.
-/

namespace MuFormulas

/-- The actions of the LTS of Example 10. -/
inductive Act
  | a | b | c
  deriving DecidableEq, Repr

/-- The fixpoint variables of Example 10. -/
inductive FixVar
  | X
  deriving DecidableEq, Repr

/-- The complete set of actions `L`, which the notes write as *true*. -/
def allActions : List Act := [.a, .b, .c]

/-- A formula over the LTS of Example 10. -/
abbrev Formula := MuFormula Act FixVar

/-- `⟨a⟩⟨b⟩⟨c⟩true`: from the initial state, a trace of an `a` action, followed by a `b`
action, followed by a `c` action is possible. -/
def traceABC : Formula := .dia .a (.dia .b (.dia .c .true))

/-- `[true*]⟨true⟩true`: after every possible trace an action is possible, i.e. the model
has no deadlocks. -/
def noDeadlock : Formula :=
  MuFormula.boxStar .X allActions (MuFormula.diaSet allActions .true)

/-- `μX.([true]X)`: there is only a finite number of steps possible from the initial state,
i.e. the model eventually terminates. -/
def terminates : Formula := .mu .X (MuFormula.boxSet allActions (.var .X))

/-- `[true*]φ` is `νX.([true]X ∧ φ)`, with `[true]X` the conjunction of `[a]X` over the
three actions. -/
theorem noDeadlock_eq :
    noDeadlock =
      .nu .X (.and (.and (.box .a (.var .X)) (.and (.box .b (.var .X))
          (.and (.box .c (.var .X)) .true)))
        (.or (.dia .a .true) (.or (.dia .b .true) (.or (.dia .c .true) .false)))) := rfl

/-- The complement shorthand: `⟨‾{a}⟩φ` is `⟨{b, c}⟩φ`. -/
theorem diaCompl_a (φ : Formula) :
    MuFormula.diaCompl allActions [.a] φ = .or (.dia .b φ) (.or (.dia .c φ) .false) := rfl

end MuFormulas
