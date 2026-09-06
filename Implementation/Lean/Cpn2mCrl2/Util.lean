/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/

/-!
# List utilities

Duplicate removal and a duplicate-freeness predicate, over a type with decidable equality.

Written out rather than taken from a library so that the verified core depends on nothing
beyond the Lean toolchain -- `Implementation/docs/Languages.md` §3 makes continuity with
`Proof/` the reason to build in Lean first, but `Proof/` needs Mathlib and a translator does
not, and keeping Mathlib out of the trust boundary and out of the binary is worth these
twenty lines.
-/

namespace Cpn2mCrl2.ListUtil

variable {α : Type} [DecidableEq α]

/-- `a` prepended to `l`, unless `l` already contains it. -/
def insertNew (a : α) (l : List α) : List α := if a ∈ l then l else a :: l

/-- `l` without repetitions, keeping the last occurrence of each item. -/
def dedup : List α → List α
  | [] => []
  | a :: as => insertNew a (dedup as)

/-- No item of `l` occurs twice. -/
def NoDup : List α → Prop
  | [] => True
  | a :: as => a ∉ as ∧ NoDup as

instance decNoDup : (l : List α) → Decidable (NoDup l)
  | [] => isTrue trivial
  | _ :: as =>
    have : Decidable (NoDup as) := decNoDup as
    inferInstanceAs (Decidable (_ ∧ _))

theorem mem_insertNew {a b : α} {l : List α} : a ∈ insertNew b l ↔ a = b ∨ a ∈ l := by
  unfold insertNew
  split
  · next h => exact ⟨Or.inr, fun ha => ha.elim (fun he => he ▸ h) id⟩
  · exact List.mem_cons

@[simp] theorem mem_dedup {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons hd tl ih => simp [dedup, mem_insertNew, ih, List.mem_cons]

theorem noDup_insertNew {a : α} {l : List α} (h : NoDup l) : NoDup (insertNew a l) := by
  unfold insertNew
  split
  · exact h
  · next ha => exact ⟨ha, h⟩

theorem noDup_dedup (l : List α) : NoDup (dedup l) := by
  induction l with
  | nil => trivial
  | cons _ _ ih => exact noDup_insertNew ih

end Cpn2mCrl2.ListUtil
