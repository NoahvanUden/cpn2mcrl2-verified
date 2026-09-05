/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Color
import Cpn2mCrl2.Util

/-!
# Bags

Definition 1 of the thesis, made finitely supported.

Definition 1 models a bag over `S` as a total function `m : S → ℕ`, and `Proof/` transcribes
it that way. `Implementation/docs/Plan.md` §4.1 requires the implementation to depart from
that:

> So the implementation's bags are finitely supported from the start. This is a further departure from Definition 1 as printed.

The reason is stated in `Thesis/docs/LeanFormalization.md` §5.1: inclusion of one total
function into another is a statement about all of `S`, which is not decidable, so the
condition of a summand could never be a `Bool`-valued *term*. Here a bag is a list of
coefficient entries, and the function Definition 1 calls the bag is recovered by `Bag.coeff`.

Every statement about bags below is phrased through `coeff`, never through the entry list:
two bags with the same coefficients are the same bag as far as Definition 1 is concerned, and
`Bag.Equiv` is that equality. The representation is deliberately not normalized -- `union` is
list append -- so the translator never has to sort or deduplicate anything.

## Main definitions

* `Bag`, `Bag.coeff` : Definition 1.
* `Bag.empty`, `Bag.single`, `Bag.union`, `Bag.diff`, `Bag.Subset` : the operations of
  Section 1.1 that Definitions 6, 7 and 14 use.
* `Bag.subsetB` : the same inclusion as a decision procedure, which is what
  `Implementation/docs/Plan.md` §4.1 says finite support is for.
-/

namespace Cpn2mCrl2

/-- **Definition 1 (Bag)**, finitely supported: a list of `(item, coefficient)` entries.

The list is not required to be duplicate-free; `Bag.coeff` sums the entries for an item, so
`⟨[(v, 1), (v, 1)]⟩` and `⟨[(v, 2)]⟩` are the same bag. -/
structure Bag where
  /-- The entries. An item may appear more than once; its coefficient is the sum. -/
  entries : List (Value × Nat)
  deriving Repr, DecidableEq

namespace Bag

/-- The coefficient of `v` in a list of entries. -/
def entryCoeff : List (Value × Nat) → Value → Nat
  | [], _ => 0
  | (u, n) :: es, v => (if u = v then n else 0) + entryCoeff es v

/-- The coefficient of `v` in `m`: the number of appearances of `v`, as Definition 1 has it.

This is the bag in the sense of Definition 1; `entries` is only a representation of it. -/
def coeff (m : Bag) (v : Value) : Nat := entryCoeff m.entries v

/-- Two bags are equal as bags when they have the same coefficients. -/
def Equiv (m₁ m₂ : Bag) : Prop := ∀ v, m₁.coeff v = m₂.coeff v

/-- The empty bag, written `∅_MS` in the thesis. -/
def empty : Bag := ⟨[]⟩

instance : EmptyCollection Bag := ⟨empty⟩

/-- The bag the thesis writes `{n`v}`: `v` with coefficient `n`, everything else with
coefficient `0`. -/
def single (n : Nat) (v : Value) : Bag := ⟨[(v, n)]⟩

/-- Operation 2, the union of two bags: the coefficients are added. -/
def union (m₁ m₂ : Bag) : Bag := ⟨m₁.entries ++ m₂.entries⟩

instance : Union Bag := ⟨union⟩

/-- The items a bag mentions, without repetition. Every item outside this list has
coefficient `0`, which is `coeff_eq_zero_of_not_mem_keys`. -/
def keys (m : Bag) : List Value := ListUtil.dedup (m.entries.map Prod.fst)

/-- Operation 6, the difference of two bags: the coefficients are subtracted and floored at
zero, which is truncated subtraction on `ℕ`. -/
def diff (m₁ m₂ : Bag) : Bag := ⟨m₁.keys.map fun v => (v, m₁.coeff v - m₂.coeff v)⟩

instance : SDiff Bag := ⟨diff⟩

/-- Operation 5, the inclusion of one bag in another: every coefficient of `m₁` is at most
the matching one of `m₂`. -/
def Subset (m₁ m₂ : Bag) : Prop := ∀ v, m₁.coeff v ≤ m₂.coeff v

instance : HasSubset Bag := ⟨Subset⟩

/-- Bag inclusion as a decision procedure.

Finite support is exactly what makes this possible: only the items `m₁` mentions have to be
checked, because its coefficient is `0` everywhere else. `subsetB_iff` is the statement that
this decides `Bag.Subset`. -/
def subsetB (m₁ m₂ : Bag) : Bool := m₁.keys.all fun v => decide (m₁.coeff v ≤ m₂.coeff v)

/-- A bag is well-typed for the color `c` when every item it mentions is. -/
def ofColor (m : Bag) (c : Color) : Bool := m.entries.all fun e => e.1.ofColor c

/-! ### The coefficient of each operation -/

@[simp] theorem coeff_empty (v : Value) : (∅ : Bag).coeff v = 0 := rfl

@[simp] theorem coeff_single (n : Nat) (u v : Value) :
    (single n u).coeff v = if u = v then n else 0 := by
  simp [single, coeff, entryCoeff]

theorem entryCoeff_append (a b : List (Value × Nat)) (v : Value) :
    entryCoeff (a ++ b) v = entryCoeff a v + entryCoeff b v := by
  induction a with
  | nil => simp [entryCoeff]
  | cons hd tl ih => cases hd; simp [entryCoeff, ih, Nat.add_assoc]

@[simp] theorem coeff_union (m₁ m₂ : Bag) (v : Value) :
    (m₁ ∪ m₂).coeff v = m₁.coeff v + m₂.coeff v :=
  entryCoeff_append _ _ v

theorem entryCoeff_eq_zero_of_not_mem (es : List (Value × Nat)) (v : Value)
    (h : v ∉ es.map Prod.fst) : entryCoeff es v = 0 := by
  induction es with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨u, n⟩ := hd
    have hu : u ≠ v := fun he => h (by simp [he])
    have htl : v ∉ tl.map Prod.fst := fun hv => h (by simp [hv])
    simp [entryCoeff, hu, ih htl]

theorem coeff_eq_zero_of_not_mem_keys {m : Bag} {v : Value} (h : v ∉ m.keys) :
    m.coeff v = 0 :=
  entryCoeff_eq_zero_of_not_mem _ _ fun hv => h (ListUtil.mem_dedup.2 hv)

theorem entryCoeff_map (ks : List Value) (f : Value → Nat) (v : Value)
    (hnd : ListUtil.NoDup ks) (hv : v ∈ ks) :
    entryCoeff (ks.map fun u => (u, f u)) v = f v := by
  induction ks with
  | nil => cases hv
  | cons hd tl ih =>
    rcases List.mem_cons.1 hv with rfl | hv'
    · have : v ∉ (tl.map fun u => (u, f u)).map Prod.fst := by simpa using hnd.1
      simp [entryCoeff, entryCoeff_eq_zero_of_not_mem _ _ this]
    · have hne : hd ≠ v := fun he => hnd.1 (he ▸ hv')
      simp [entryCoeff, hne, ih hnd.2 hv']

@[simp] theorem coeff_diff (m₁ m₂ : Bag) (v : Value) :
    (m₁ \ m₂).coeff v = m₁.coeff v - m₂.coeff v := by
  by_cases hv : v ∈ m₁.keys
  · exact entryCoeff_map _ _ _ (ListUtil.noDup_dedup _) hv
  · have h₁ : m₁.coeff v = 0 := coeff_eq_zero_of_not_mem_keys hv
    have h₂ : v ∉ (m₁.keys.map fun u => (u, m₁.coeff u - m₂.coeff u)).map Prod.fst := by
      simpa using hv
    have hd : (m₁ \ m₂).entries = m₁.keys.map fun u => (u, m₁.coeff u - m₂.coeff u) := rfl
    show entryCoeff (m₁ \ m₂).entries v = _
    rw [hd, entryCoeff_eq_zero_of_not_mem _ _ h₂, h₁, Nat.zero_sub]

/-! ### Inclusion -/

@[simp] theorem subset_def {m₁ m₂ : Bag} : m₁ ⊆ m₂ ↔ ∀ v, m₁.coeff v ≤ m₂.coeff v := Iff.rfl

/-- `subsetB` decides `Bag.Subset`. Only the items `m₁` mentions need checking, since its
coefficient is zero everywhere else. -/
theorem subsetB_iff (m₁ m₂ : Bag) : subsetB m₁ m₂ = true ↔ m₁ ⊆ m₂ := by
  constructor
  · intro h v
    by_cases hv : v ∈ m₁.keys
    · exact of_decide_eq_true (List.all_eq_true.1 h v hv)
    · simp [coeff_eq_zero_of_not_mem_keys hv]
  · intro h
    exact List.all_eq_true.2 fun v _ => decide_eq_true (h v)

instance (m₁ m₂ : Bag) : Decidable (m₁ ⊆ m₂) :=
  decidable_of_iff _ (subsetB_iff m₁ m₂)

/-! ### `Equiv` is an equivalence, and the operations respect it -/

theorem Equiv.rfl (m : Bag) : Equiv m m := fun _ => Eq.refl _

theorem Equiv.symm {m₁ m₂ : Bag} (h : Equiv m₁ m₂) : Equiv m₂ m₁ := fun v => (h v).symm

theorem Equiv.trans {m₁ m₂ m₃ : Bag} (h₁ : Equiv m₁ m₂) (h₂ : Equiv m₂ m₃) : Equiv m₁ m₃ :=
  fun v => (h₁ v).trans (h₂ v)

theorem Equiv.union {m₁ m₂ n₁ n₂ : Bag} (h₁ : Equiv m₁ n₁) (h₂ : Equiv m₂ n₂) :
    Equiv (m₁ ∪ m₂) (n₁ ∪ n₂) := by intro v; simp [h₁ v, h₂ v]

theorem Equiv.diff {m₁ m₂ n₁ n₂ : Bag} (h₁ : Equiv m₁ n₁) (h₂ : Equiv m₂ n₂) :
    Equiv (m₁ \ m₂) (n₁ \ n₂) := by intro v; simp [h₁ v, h₂ v]

theorem Equiv.subset {m₁ m₂ n₁ n₂ : Bag} (h₁ : Equiv m₁ n₁) (h₂ : Equiv m₂ n₂)
    (h : m₁ ⊆ m₂) : n₁ ⊆ n₂ := fun v => by rw [← h₁ v, ← h₂ v]; exact h v

end Bag

end Cpn2mCrl2
