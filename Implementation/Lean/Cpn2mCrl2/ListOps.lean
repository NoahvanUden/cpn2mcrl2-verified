/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Bag

/-!
# Lists as bags

The multiset operations a list-encoded marking needs, and what they do to the bag the list
represents.

`Thesis/docs/mCRL2.md` §4.1 measures the reason this file exists:

| Marking representation | Average time |
| --- | --- |
| `Bag` | 67 seconds |
| `FBag` | 60 seconds |
| `List` | 9 seconds |

`Implementation/docs/Plan.md` §5 turns that sevenfold speedup into the project's largest open
question, because a list is not a bag:

> A list-encoded marking is a *representative* of a bag, and the translation must be invariant under which representative it holds.

Everything here is about that word *representative*. `bagOfList` is the map from a list to the
bag it represents; `eraseFirst`, `listDiff` and `subMultiset` are the list operations mCRL2 can
do quickly; and each is shown to compute, on the represented bag, exactly the operation of
Definition 1 that the bag encoding uses. Two lists with the same `bagOfList` are therefore
indistinguishable to the translation, which is the content of the order half of `Plan.md` §5.

## Main results

* `coeff_bagOfList` : the bag a list represents counts occurrences.
* `countOf_append`, `countOf_listDiff`, `subMultiset_iff` : the three operations against
  Definition 1's `∪`, `\` and `⊆`.
-/

namespace Cpn2mCrl2

/-! ## Counting -/

/-- The number of times `v` occurs in `l`. -/
def countOf : List Value → Value → Nat
  | [], _ => 0
  | u :: us, v => (if u = v then 1 else 0) + countOf us v

/-- The bag a list represents: every element with multiplicity one, so that the coefficient of
an item is the number of times the list holds it. -/
def bagOfList (l : List Value) : Bag := ⟨l.map fun v => (v, 1)⟩

@[simp] theorem countOf_nil (v : Value) : countOf [] v = 0 := rfl

@[simp] theorem countOf_cons_self (u : Value) (us : List Value) :
    countOf (u :: us) u = 1 + countOf us u := by simp [countOf]

theorem countOf_cons_of_ne {u v : Value} (h : u ≠ v) (us : List Value) :
    countOf (u :: us) v = countOf us v := by simp [countOf, h]

@[simp] theorem coeff_bagOfList (l : List Value) (v : Value) :
    (bagOfList l).coeff v = countOf l v := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    show Bag.entryCoeff ((u, 1) :: _) v = _
    show (if u = v then 1 else 0) + Bag.entryCoeff (us.map fun w => (w, 1)) v = _
    rw [show Bag.entryCoeff (us.map fun w => (w, 1)) v = (bagOfList us).coeff v from rfl, ih]
    rfl

theorem countOf_append (a b : List Value) (v : Value) :
    countOf (a ++ b) v = countOf a v + countOf b v := by
  induction a with
  | nil => simp
  | cons u us ih =>
    by_cases hu : u = v
    · subst hu
      simp only [List.cons_append, countOf_cons_self, ih, Nat.add_assoc]
    · simp only [List.cons_append, countOf_cons_of_ne hu, ih]

theorem mem_iff_countOf {l : List Value} {v : Value} : v ∈ l ↔ 0 < countOf l v := by
  induction l with
  | nil => simp
  | cons u us ih =>
    rw [List.mem_cons]
    by_cases hu : u = v
    · subst hu
      rw [countOf_cons_self]
      exact ⟨fun _ => by omega, fun _ => Or.inl rfl⟩
    · rw [countOf_cons_of_ne hu]
      exact ⟨fun hv => hv.elim (fun he => absurd he.symm hu) ih.1, fun hv => Or.inr (ih.2 hv)⟩

/-! ## Removing -/

/-- `l` with the first occurrence of `v` dropped, which is mCRL2's `rm`. -/
def eraseFirst : List Value → Value → List Value
  | [], _ => []
  | u :: us, v => if u = v then us else u :: eraseFirst us v

@[simp] theorem eraseFirst_nil (v : Value) : eraseFirst [] v = [] := rfl

@[simp] theorem eraseFirst_cons_self (u : Value) (us : List Value) :
    eraseFirst (u :: us) u = us := by simp [eraseFirst]

theorem eraseFirst_cons_of_ne {u x : Value} (h : u ≠ x) (us : List Value) :
    eraseFirst (u :: us) x = u :: eraseFirst us x := by simp [eraseFirst, h]

theorem mem_of_mem_eraseFirst {l : List Value} {x v : Value} (h : v ∈ eraseFirst l x) :
    v ∈ l := by
  induction l with
  | nil => exact h
  | cons u us ih =>
    by_cases hu : u = x
    · subst hu
      rw [eraseFirst_cons_self] at h
      exact List.mem_cons_of_mem _ h
    · rw [eraseFirst_cons_of_ne hu] at h
      rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h')

theorem countOf_eraseFirst_self (l : List Value) (x : Value) :
    countOf (eraseFirst l x) x = countOf l x - 1 := by
  induction l with
  | nil => simp
  | cons u us ih =>
    by_cases hu : u = x
    · subst hu
      rw [eraseFirst_cons_self, countOf_cons_self]
      omega
    · rw [eraseFirst_cons_of_ne hu, countOf_cons_of_ne hu, countOf_cons_of_ne hu, ih]

theorem countOf_eraseFirst_of_ne {x v : Value} (h : x ≠ v) (l : List Value) :
    countOf (eraseFirst l x) v = countOf l v := by
  induction l with
  | nil => simp
  | cons u us ih =>
    by_cases hu : u = x
    · subst hu
      rw [eraseFirst_cons_self, countOf_cons_of_ne h]
    · rw [eraseFirst_cons_of_ne hu]
      by_cases huv : u = v
      · subst huv
        rw [countOf_cons_self, countOf_cons_self, ih]
      · rw [countOf_cons_of_ne huv, countOf_cons_of_ne huv, ih]

theorem countOf_eraseFirst (l : List Value) (x v : Value) :
    countOf (eraseFirst l x) v = countOf l v - (if x = v then 1 else 0) := by
  by_cases h : x = v
  · subst h; simpa using countOf_eraseFirst_self l x
  · simpa [h] using countOf_eraseFirst_of_ne h l

/-- Multiset difference: `a` with one occurrence of each element of `b` dropped. -/
def listDiff : List Value → List Value → List Value
  | a, [] => a
  | a, x :: b => listDiff (eraseFirst a x) b

theorem mem_of_mem_listDiff : ∀ {b a : List Value} {v : Value}, v ∈ listDiff a b → v ∈ a
  | [], _, _, h => h
  | _ :: b, _, _, h => mem_of_mem_eraseFirst (mem_of_mem_listDiff (b := b) h)

theorem countOf_listDiff : ∀ (b a : List Value) (v : Value),
    countOf (listDiff a b) v = countOf a v - countOf b v
  | [], a, v => by simp [listDiff]
  | x :: b, a, v => by
    rw [show listDiff a (x :: b) = listDiff (eraseFirst a x) b from rfl,
      countOf_listDiff b (eraseFirst a x) v, countOf_eraseFirst a x v, countOf, Nat.sub_sub]

/-! ## Inclusion -/

/-- Multiset inclusion: every element of `a` can be matched with a distinct element of `b`. -/
def subMultiset : List Value → List Value → Bool
  | [], _ => true
  | x :: a, b => decide (x ∈ b) && subMultiset a (eraseFirst b x)

/-- **The list operations compute Definition 1's operations on the bag the list represents.**

This one is the inclusion of operation 5; `countOf_append` and `countOf_listDiff` are
operations 2 and 6. Together they are what makes a list a faithful representative, and so what
makes the list encoding a candidate refinement of the bag encoding at all. -/
theorem subMultiset_iff : ∀ (a b : List Value),
    subMultiset a b = true ↔ ∀ v, countOf a v ≤ countOf b v
  | [], b => by simp [subMultiset]
  | x :: a, b => by
    rw [show subMultiset (x :: a) b = (decide (x ∈ b) && subMultiset a (eraseFirst b x)) from rfl,
      Bool.and_eq_true, decide_eq_true_iff, subMultiset_iff a (eraseFirst b x)]
    constructor
    · rintro ⟨hx, hrest⟩ v
      by_cases hxv : x = v
      · subst hxv
        have hpos : 0 < countOf b x := mem_iff_countOf.1 hx
        have hb := hrest x
        rw [countOf_eraseFirst_self] at hb
        rw [countOf_cons_self]
        omega
      · have hb := hrest v
        rw [countOf_eraseFirst_of_ne hxv] at hb
        rw [countOf_cons_of_ne hxv]
        exact hb
    · intro hle
      have hx0 := hle x
      rw [countOf_cons_self] at hx0
      refine ⟨mem_iff_countOf.2 (by omega), fun v => ?_⟩
      by_cases hxv : x = v
      · subst hxv
        rw [countOf_eraseFirst_self]
        omega
      · rw [countOf_eraseFirst_of_ne hxv]
        have hv := hle v
        rw [countOf_cons_of_ne hxv] at hv
        exact hv

end Cpn2mCrl2
