/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Mathlib.Data.Fintype.Basic
import Proof.Bisimulation

/-!
# A tennis game: 30-30 is bisimilar to deuce

A game of tennis as an `LTS`: the states are the possible scores, the two actions are "the
next point goes to player A" and "the next point goes to player B", and the initial state is
love-all.

In this LTS the score 30-30 and the score 40-40 (deuce) are bisimilar, which is why the two
are the same position from the players' point of view: from either one, whoever takes the
next point needs one more point to win the game, and whoever loses it is back at a score
bisimilar to the one they started from.

The bisimulation relation `rel` witnessing it is equality together with the three pairs

    30-30 R deuce,    40-30 R advantage A,    30-40 R advantage B

and Definition 16 is checked for it by `decide`.

This is an example of `Proof/Bisimulation.lean` (Definition 16 of the thesis *Model checking
for analysis of BPMN models*, N. van Uden, TU/e, 2025); the tennis game itself is not from
the thesis.
-/

namespace Tennis

open scoped LTS

/-- The player who wins a point. -/
inductive Player
  | a | b
  deriving DecidableEq, Repr

/-- The score of a game of tennis, from the point of view of player A: `fortyThirty` is
"40-30 to A", `advA` is "advantage A", `gameA` is "game to A". -/
inductive Score
  | loveAll | fifteenLove | loveFifteen | fifteenAll
  | thirtyLove | loveThirty | thirtyFifteen | fifteenThirty
  | fortyLove | loveForty | thirtyAll
  | fortyFifteen | fifteenForty | fortyThirty | thirtyForty
  | deuce | advA | advB | gameA | gameB
  deriving DecidableEq, Repr

instance : Fintype Player := ⟨{.a, .b}, fun x => by cases x <;> decide⟩

instance : Fintype Score :=
  ⟨{.loveAll, .fifteenLove, .loveFifteen, .fifteenAll,
    .thirtyLove, .loveThirty, .thirtyFifteen, .fifteenThirty,
    .fortyLove, .loveForty, .thirtyAll,
    .fortyFifteen, .fifteenForty, .fortyThirty, .thirtyForty,
    .deuce, .advA, .advB, .gameA, .gameB}, fun x => by cases x <;> decide⟩

/-- The score after the given player wins the next point, or `none` once the game is over. -/
def next : Score → Player → Option Score
  | .loveAll, .a => some .fifteenLove
  | .loveAll, .b => some .loveFifteen
  | .fifteenLove, .a => some .thirtyLove
  | .fifteenLove, .b => some .fifteenAll
  | .loveFifteen, .a => some .fifteenAll
  | .loveFifteen, .b => some .loveThirty
  | .fifteenAll, .a => some .thirtyFifteen
  | .fifteenAll, .b => some .fifteenThirty
  | .thirtyLove, .a => some .fortyLove
  | .thirtyLove, .b => some .thirtyFifteen
  | .loveThirty, .a => some .fifteenThirty
  | .loveThirty, .b => some .loveForty
  | .thirtyFifteen, .a => some .fortyFifteen
  | .thirtyFifteen, .b => some .thirtyAll
  | .fifteenThirty, .a => some .thirtyAll
  | .fifteenThirty, .b => some .fifteenForty
  | .fortyLove, .a => some .gameA
  | .fortyLove, .b => some .fortyFifteen
  | .loveForty, .a => some .fifteenForty
  | .loveForty, .b => some .gameB
  | .thirtyAll, .a => some .fortyThirty
  | .thirtyAll, .b => some .thirtyForty
  | .fortyFifteen, .a => some .gameA
  | .fortyFifteen, .b => some .fortyThirty
  | .fifteenForty, .a => some .thirtyForty
  | .fifteenForty, .b => some .gameB
  | .fortyThirty, .a => some .gameA
  | .fortyThirty, .b => some .deuce
  | .thirtyForty, .a => some .deuce
  | .thirtyForty, .b => some .gameB
  | .deuce, .a => some .advA
  | .deuce, .b => some .advB
  | .advA, .a => some .gameA
  | .advA, .b => some .deuce
  | .advB, .a => some .deuce
  | .advB, .b => some .gameB
  | .gameA, _ => none
  | .gameB, _ => none

/-- A game of tennis as an LTS: the scores are the states, a point to one of the players is
an action, and love-all is the initial state. -/
def game : LTS Score Player where
  step s p s' := next s p = some s'
  init := .loveAll

instance (s : Score) (p : Player) (s' : Score) : Decidable (game ⊢ s -[p]→ s') :=
  inferInstanceAs (Decidable (next s p = some s'))

/-- The candidate bisimulation: equality, together with 30-30 against deuce and the two
scores one point from the game against the matching advantage. -/
def rel : Score → Score → Bool
  | .thirtyAll, .deuce => true
  | .fortyThirty, .advA => true
  | .thirtyForty, .advB => true
  | s, s' => decide (s = s')

/-- `rel` satisfies both conditions of Definition 16, checked over all 20 scores, both
players and all successor scores. -/
theorem bisimulation_rel : LTS.Bisimulation game game (fun s s' => rel s s') := by
  unfold LTS.Bisimulation
  decide

/-- **30-30 is bisimilar to deuce.** -/
theorem thirtyAll_bisimilar_deuce : LTS.BisimilarStates game game .thirtyAll .deuce :=
  ⟨_, bisimulation_rel, rfl⟩

/-- The scores that carry the bisimilarity of 30-30 and deuce one point further: 40-30 is
bisimilar to advantage A, ... -/
theorem fortyThirty_bisimilar_advA : LTS.BisimilarStates game game .fortyThirty .advA :=
  ⟨_, bisimulation_rel, rfl⟩

/-- ... and 30-40 is bisimilar to advantage B. -/
theorem thirtyForty_bisimilar_advB : LTS.BisimilarStates game game .thirtyForty .advB :=
  ⟨_, bisimulation_rel, rfl⟩

/-- Not every pair of scores is bisimilar. 30-30 is not bisimilar to 40-30: from 40-30 a
point to A wins the game, and 30-30 can only answer with 40-30, so any bisimulation would
have to relate 40-30 to the finished game -- and then the winning point of 40-30 has no
answer at all, because a finished game has no moves left. -/
theorem not_bisimilarStates_thirtyAll_fortyThirty :
    ¬ LTS.BisimilarStates game game .thirtyAll .fortyThirty := by
  rintro ⟨R, hR, h⟩
  obtain ⟨u, hstep, hRu⟩ := hR.2 .thirtyAll .fortyThirty .gameA .a rfl h
  have hu : u = .fortyThirty := by clear hRu; revert u; decide
  subst hu
  obtain ⟨u', hstep', -⟩ := hR.1 .fortyThirty .gameA .gameA .a rfl hRu
  simp [game, next] at hstep'

/-- The two steps out of 30-30 and the two steps out of deuce that the bisimulation matches
up: a point to A gives 40-30 against advantage A, ... -/
example : game ⊢ .thirtyAll -[.a]→ .fortyThirty := rfl

example : game ⊢ .deuce -[.a]→ .advA := rfl

/-- ... and a point to B gives 30-40 against advantage B. -/
example : game ⊢ .thirtyAll -[.b]→ .thirtyForty := rfl

example : game ⊢ .deuce -[.b]→ .advB := rfl

/-- Losing the next point from either 40-30 or advantage A returns to deuce, which is what
makes the whole relation close up. -/
example : game ⊢ .fortyThirty -[.b]→ .deuce := rfl

example : game ⊢ .advA -[.b]→ .deuce := rfl

end Tennis
