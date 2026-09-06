/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Common definitions

Definitions 1 and 2 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025), Chapter 2 (*Mathematical preliminaries*), together with the
expression language that Chapter 2 assumes is provided by the modelling tools.

See `Thesis/docs/CommonDefinitions.md` for the prose version.

## Main definitions

* `Bag S` : Definition 1, a bag over `S`, with the six operations of Section 1.1.
* `Bindings` : Definition 2, the bindings `B[V]` of a set of variables `V`.
* `ExprLang` : the assumed expression language -- `EXPR`, `Type[.]`, `VAR[.]` and
  evaluation of an expression under a binding -- packaged as a structure.
-/

universe u v w x

/-! ## Bags -/

/-- **Definition 1 (Bag).**
A bag `m` over a non-empty set `S` is a function `m : S → ℕ`, where for each `s ∈ S`,
`m s` is the number of appearances of `s` in `m`, also called the coefficient of `s`.

The thesis requires `S` to be non-empty; that requirement plays no role in any of the
operations or in the definitions that use bags, so it is not carried here. -/
def Bag (S : Type u) : Type u := S → ℕ

namespace Bag

variable {S : Type u}

/-- The coefficient of `s` in `m`. -/
def coeff (m : Bag S) (s : S) : ℕ := m s

/-- Membership: `s` is in `m` if and only if its coefficient is positive. -/
instance : Membership S (Bag S) := ⟨fun m s => 0 < m s⟩

/-- The bag containing no elements. -/
instance : EmptyCollection (Bag S) := ⟨fun _ => 0⟩

/-- Addition: the coefficients of the two bags are added. -/
instance : Union (Bag S) := ⟨fun m₁ m₂ s => m₁ s + m₂ s⟩

/-- Comparison: every coefficient of the first bag is at most the matching one of the
second. -/
instance : HasSubset (Bag S) := ⟨fun m₁ m₂ => ∀ s, m₁ s ≤ m₂ s⟩

/-- Subtraction: the coefficients are subtracted, floored at zero, which is exactly
truncated subtraction on `ℕ`. -/
instance : SDiff (Bag S) := ⟨fun m₁ m₂ s => m₁ s - m₂ s⟩

@[simp] theorem mem_def {m : Bag S} {s : S} : s ∈ m ↔ 0 < m s := Iff.rfl

@[simp] theorem empty_apply (s : S) : (∅ : Bag S) s = 0 := rfl

@[simp] theorem union_apply (m₁ m₂ : Bag S) (s : S) : (m₁ ∪ m₂) s = m₁ s + m₂ s := rfl

@[simp] theorem subset_def {m₁ m₂ : Bag S} : m₁ ⊆ m₂ ↔ ∀ s, m₁ s ≤ m₂ s := Iff.rfl

@[simp] theorem sdiff_apply (m₁ m₂ : Bag S) (s : S) : (m₁ \ m₂) s = m₁ s - m₂ s := rfl

@[ext] theorem ext {m₁ m₂ : Bag S} (h : ∀ s, m₁ s = m₂ s) : m₁ = m₂ := funext h

/-- The bag in which `s` has coefficient `n` and every other item has coefficient `0`,
written in the thesis with a backquote between the coefficient and the item. -/
def single [DecidableEq S] (n : ℕ) (s : S) : Bag S := fun x => if x = s then n else 0

@[simp] theorem single_apply [DecidableEq S] (n : ℕ) (s x : S) :
    single n s x = if x = s then n else 0 := rfl

/-- Size: the sum of all coefficients.

The thesis states this sum over an arbitrary `S`, which need not be finite; it is therefore
valued in `ℕ∞` here, as the supremum of the finite partial sums. For a bag with finite
support this is the ordinary sum. -/
noncomputable def card (m : Bag S) : ℕ∞ := ⨆ F : Finset S, ((∑ s ∈ F, m s : ℕ) : ℕ∞)

/-- Summation: the coefficient of `s` in the union of a family of bags is the sum of its
coefficients in the members of the family.

The thesis writes this for a family indexed by `ℕ` and leaves well-definedness implicit:
the result has to be a bag, so the sum has to be finite, i.e. each item may occur in only
finitely many of the `m i`. That hypothesis is `h` here. -/
noncomputable def iUnion {ι : Type v} (m : ι → Bag S) (h : ∀ s, {i | m i s ≠ 0}.Finite) :
    Bag S :=
  fun s => ∑ i ∈ (h s).toFinset, m i s

end Bag

/-! ## Bindings -/

/-- **Definition 2 (Binding).**
A binding of a set of variables `V` is a function `b` that maps each variable `v ∈ V` to a
concrete value `b v` of type `Type[v]`. `Bindings val varType V` is the set of all bindings
of `V`, where `varType` is `Type[.]` on variables and `val c` is the set of values of the
color `c`. -/
def Bindings {Color : Type u} {Var : Type w} (val : Color → Type v) (varType : Var → Color)
    (V : Set Var) : Type (max v w) :=
  (v : V) → val (varType v.1)

/-! ## Expressions

Chapter 2 assumes that the tools in which the formalisms are modelled provide an expression
language, and uses `EXPR`, `Type[e]`, `VAR[e]`, `EXPR_V` and evaluation of an expression
under a binding without fixing any of them. `ExprLang` below packages exactly those
assumptions, so that everything downstream is stated for an arbitrary expression language
rather than for one particular choice.

The one departure is `Type[.]`: instead of a function from expressions to types, the type
of an expression is the *index* of the family `Expr`, so `Expr τ` is what the thesis writes
as the expressions `e` with `Type[e] = τ`. This is what makes the typing side conditions of
Definition 5 (the guard is boolean, an arc expression is a bag of the color of its place)
hold by construction, instead of needing a cast at every evaluation. -/

/-- The types an expression can have: a color `c`, or the bag of a color, written `c_MS` in
the thesis. -/
inductive ExprTy (Color : Type u) where
  /-- The type of an expression evaluating to a single value of color `c`. -/
  | color (c : Color)
  /-- The type of an expression evaluating to a bag of values of color `c`. -/
  | bag (c : Color)
  deriving DecidableEq

/-- The values an expression of type `τ` can evaluate to, given the values `val c` of each
color `c`.

Marked `@[reducible]`, so that a concrete instantiation of it -- `Bag ℤ`, say -- is found
by instance search. -/
@[reducible] def ExprTy.Value {Color : Type u} (val : Color → Type v) : ExprTy Color → Type v
  | .color c => val c
  | .bag c => Bag (val c)

/-- The expression language assumed in Chapter 2 of the thesis: a set of colors with their
values, a set of typed variables, the expressions `EXPR` with their free variables, and the
evaluation of an expression under a binding. -/
structure ExprLang where
  /-- The colors (types) provided by the language. -/
  Color : Type u
  /-- The values of each color. -/
  val : Color → Type v
  /-- It is assumed that the set of colors contains at least the type `Bool`, ... -/
  boolColor : Color
  /-- ... whose values are the booleans. -/
  boolVal : val boolColor ≃ Bool
  /-- The variables of the language. -/
  Var : Type w
  /-- The type of a variable. -/
  varType : Var → Color
  /-- `EXPR`, indexed by the type of the expression. -/
  Expr : ExprTy Color → Type x
  /-- The free variables of an expression. -/
  vars : ∀ {τ : ExprTy Color}, Expr τ → Set Var
  /-- The evaluation of an expression under a binding of its free variables. -/
  eval : ∀ {τ : ExprTy Color} (e : Expr τ), Bindings val varType (vars e) → τ.Value val

namespace ExprLang

variable (L : ExprLang)

/-- The bindings of a set of variables `V`. -/
def Binding (V : Set L.Var) : Type _ := Bindings L.val L.varType V

/-- `EXPR_V`, the expressions of type `τ` whose free variables are contained in `V`.

Marked `@[reducible]`, for the same reason as `ExprTy.Value`: an expression paired with a
proof about its free variables should be recognised as a subtype without unfolding, so that
a term built from one -- `CPN.Term.expr`, say -- rewrites with its evaluation equation. -/
@[reducible] def ExprOn (V : Set L.Var) (τ : ExprTy L.Color) : Type _ :=
  {e : L.Expr τ // L.vars e ⊆ V}

variable {L}

/-- The evaluation of `e` under a binding `b` of any set of variables containing the free
variables of `e`. Definitions 6 and 7 evaluate the guard and the arc expressions of a
transition `t` under a binding of `Var(t)`, which is in general larger than the free
variables of the individual expression. -/
def evalOn {V : Set L.Var} {τ : ExprTy L.Color} (e : L.Expr τ) (h : L.vars e ⊆ V)
    (b : L.Binding V) : τ.Value L.val :=
  L.eval e fun v => b ⟨v.1, h v.2⟩

/-- The only binding of no variables, used to evaluate the expressions of `EXPR_∅`. -/
def emptyBinding : L.Binding (∅ : Set L.Var) := fun v => v.2.elim

/-- The evaluation of an expression without free variables. -/
def evalClosed {τ : ExprTy L.Color} (e : L.ExprOn ∅ τ) : τ.Value L.val :=
  evalOn e.1 e.2 emptyBinding

/-- A boolean expression evaluates to `True` under a binding `b`. -/
def Holds {V : Set L.Var} (e : L.Expr (.color L.boolColor)) (h : L.vars e ⊆ V)
    (b : L.Binding V) : Prop :=
  L.boolVal (evalOn e h b) = true

end ExprLang
