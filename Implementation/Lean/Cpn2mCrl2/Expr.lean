/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Bag

/-!
# The expression language

`EXPR` of Chapter 2, fixed concretely by `Implementation/docs/InputFormat.md` §4.1, plus the
two things Definition 14 needs that a CPN file never contains: bag inclusion, and variables of
bag sort.

`Proof/CommonDefinitions.lean` leaves the expression language abstract, as the thesis does:
`ExprLang` is a structure whose `Expr` field is any family with free variables and an
evaluation. A program cannot do that -- `Implementation/docs/Plan.md` §3 says so directly --
so `Expr` here is one inductive family, and it is the *same* family on both sides of the
translation: a CPN's guards and arc expressions are `Expr`s, and the terms Definition 14
assembles are `Expr`s too. That is what makes the T2 obligation statable at all.

## Implementation notes

**Typing is intrinsic, scoping is not.** `Expr` is indexed by `ExprTy`, so a guard is a
boolean expression and an arc expression is a bag expression by construction -- checks 4 to 6
of `Implementation/docs/InputFormat.md` §4.3 hold for every `Expr` that exists. Variables, by
contrast, carry only their name and sort, and `Expr.freeVars` reports which they are; being in
scope is the separate predicate `Expr.ScopedIn`, which is check 7.

The alternative -- indexing `Expr` by a context and having each variable carry a membership
proof -- makes a term depend on the exact context it was built in, and Definition 14 builds
terms in a *different* context from the one the CPN's expressions live in: the summand's
context is one place parameter per place together with `Var(t)`, and `Var(t)` is generally
smaller than `V`. With intrinsic scoping the translation would have to re-index every subterm
and obligation 4 of `Implementation/docs/Plan.md` §4 would be a strengthening lemma over
dependent proofs. With extrinsic scoping the translation moves a term between contexts by
doing nothing to it at all, and obligation 4 is `Expr.eval_congr` below: the value of an
expression depends only on its free variables.

Nothing is given up. Scoping is still checked, at the boundary where
`Implementation/docs/InputFormat.md` §4.3 puts it, and `Cpn2mCrl2/Translate.lean` proves that
every term the translation emits is scoped in the context the emitted text binds.

**Variables carry an `ExprTy`, not a `Color`.** Definition 5 types every variable of `V` by a
color, and `Proof/CommonDefinitions.lean` has `varType : Var → Color` accordingly. But
Definition 14's state `d` is a tuple of *bags*, one per place, so the terms it builds mention
bag-sorted variables. Rather than the product former of
`Thesis/docs/LeanFormalization.md` §5.1, the tuple is realized as mCRL2's own parameter list
and its components as ordinary variables -- which needs nothing more than allowing a variable
to have bag sort. A CPN file still only ever declares color-sorted variables; that is
`Net.varsAreColors` in `Cpn2mCrl2/Net.lean`.

**Environments are total and dependent.** `Env` assigns a value of the right shape to every
sort-and-name pair, which is what removes membership proofs from `Expr.eval`. Definition 2's
`B[V]` is the restriction of this to `V`, and `Expr.eval_congr` says the restriction is all an
expression can see.

**Junk values.** `Value` is untyped, so `eval` has to give an answer when a subexpression
evaluates to the wrong shape -- `Value.asInt` and friends supply one.
`Cpn2mCrl2/Typing.lean` proves the case never arises when the environment is well-typed.

## Main definitions

* `Expr` : `EXPR`, indexed by `ExprTy`.
* `Expr.eval` : evaluation under a binding, the thesis's `e⟨b⟩`.
* `Expr.freeVars`, `Expr.ScopedIn` : `VAR[e]`, and check 7 of `InputFormat.md` §4.3.
* `Expr.eval_congr` : obligation 4 of `Plan.md` §4.
-/

namespace Cpn2mCrl2

/-- The type of an expression: a color `c`, or the bag of a color, written `c_MS` in the
thesis.

The two constructors of `Proof/CommonDefinitions.lean`'s `ExprTy`, unchanged.
`Thesis/docs/LeanFormalization.md` §5.1 predicts a third, a product former, because `D` and
`H_t` of Definition 13 are tuple-sorted. It is not needed here: see `Cpn2mCrl2/Lpe.lean`,
where both tuples are realized as mCRL2 binder lists rather than as sorts of a term. -/
inductive ExprTy where
  /-- The type of an expression evaluating to a single value of color `c`. -/
  | color (c : Color)
  /-- The type of an expression evaluating to a bag of values of color `c`. -/
  | bag (c : Color)
  deriving DecidableEq, Repr

/-- A typing context: the variables in scope, with their sorts. `V` of Definition 5 together
with `Type[.]` is one of these, in which every entry is a `.color`. -/
abbrev Ctx := List (String × ExprTy)

/-- What an expression of type `τ` evaluates to.

Marked `@[reducible]`, as `Proof/CommonDefinitions.lean` marks `ExprTy.Value`, so that
instance search sees through it to `Bag`. -/
@[reducible] def ExprTy.Denot : ExprTy → Type
  | .color _ => Value
  | .bag _ => Bag

/-- The color underlying a sort. -/
def ExprTy.color! : ExprTy → Color
  | .color c => c
  | .bag c => c

/-- Whether a sort is a color rather than a bag.

Definition 5 types every variable of `V` by a color; `Net.Valid.varsAreColors` says so with
this rather than with `∃ c, τ = .color c`, because the existential ranges over `Color` and is
not decidable, and the whole point of `Net.Valid` is that the importer can check it. -/
def ExprTy.isColor : ExprTy → Bool
  | .color _ => true
  | .bag _ => false

theorem ExprTy.eq_color_of_isColor : ∀ {τ : ExprTy}, τ.isColor = true → τ = .color τ.color!
  | .color _, _ => rfl

/-- A value of the right shape for the sort `τ` -- a well-typed value of its color, or a bag
whose items all are. -/
def ExprTy.Wf : (τ : ExprTy) → τ.Denot → Prop
  | .color c, v => v.ofColor c = true
  | .bag c, m => m.ofColor c = true

/-! ## Reading a value at a shape

`Value` is untyped, so evaluation of `1 + e` has to do something when `e` is not an integer.
These give the value a well-typed environment guarantees, and junk otherwise. -/

/-- The integer a value carries, or `0`. -/
def Value.asInt : Value → Int
  | .int i => i
  | _ => 0

/-- The boolean a value carries, or `false`. -/
def Value.asBool : Value → Bool
  | .bool b => b
  | _ => false

/-- The fields a record value carries, or none. -/
def Value.asRecord : Value → ValueFields
  | .record vs => vs
  | _ => .nil

/-! ## Environments -/

/-- A binding: a value of the right shape for every sort and name.

Definition 2's `B[V]` is the restriction of this to the variables of `V`; `Expr.eval_congr`
says an expression cannot tell the difference between two environments that agree on its free
variables, which is what makes the restriction harmless. -/
def Env := (τ : ExprTy) → String → τ.Denot

/-- The environment binding every variable to junk. -/
def Env.junk : Env
  | .color c, _ => c.junk
  | .bag _, _ => ∅

/-- An environment is well-typed when every variable holds a value of its own sort. -/
def Env.Wf (env : Env) : Prop := ∀ (τ : ExprTy) (x : String), τ.Wf (env τ x)

/-! ## Expressions -/

mutual

/-- `EXPR` of `Implementation/docs/InputFormat.md` §4.1, indexed by the type of the
expression.

Three constructors depart from that grammar and are worth naming.

`var` may have bag sort. A CPN file never produces one; Definition 14's place parameters are
the only bag-sorted variables that occur, and `Cpn2mCrl2/Net.lean` records that a net's own
variables are all color-sorted.

`bagSubset` is the operation Definition 14 uses and a CPN file never contains. It is here so
that *one* language serves both as the annotation language of a CPN and as the mCRL2 data
language the translation emits into, which is obligation 2 of
`Implementation/docs/Plan.md` §4. `Cpn2mCrl2/Json.lean` does not parse it.

`single` replaces the grammar's `bag([(n, e), ...])`. A bag literal with several items is the
union of its singletons, which is how Definition 1 builds it anyway, and it keeps the
constructor free of a nested list. `Cpn2mCrl2/Json.lean` desugars the literal. -/
inductive Expr : ExprTy → Type where
  /-- A variable, at any sort. -/
  | var (x : String) (τ : ExprTy) : Expr τ
  /-- An integer literal. -/
  | intLit (n : Int) : Expr (.color .int)
  /-- A boolean literal. -/
  | boolLit (b : Bool) : Expr (.color .bool)
  /-- A constructor of an enumeration. -/
  | ctorLit (name : String) (ids : List String) (id : String) (h : id ∈ ids) :
      Expr (.color (.enum name ids))
  /-- A record, built from one expression per field. -/
  | mkRec (name : String) {fs : ColorFields} (args : Args fs) :
      Expr (.color (.record name fs))
  /-- The projection of a field out of a record. -/
  | proj {name : String} {fs : ColorFields} (e : Expr (.color (.record name fs)))
      (f : String) (c : Color) (h : fs.lookup f = some c) : Expr (.color c)
  /-- Integer addition. -/
  | add (a b : Expr (.color .int)) : Expr (.color .int)
  /-- Integer subtraction. -/
  | sub (a b : Expr (.color .int)) : Expr (.color .int)
  /-- Integer multiplication. -/
  | mul (a b : Expr (.color .int)) : Expr (.color .int)
  /-- Equality at a color. -/
  | eq {c : Color} (a b : Expr (.color c)) : Expr (.color .bool)
  /-- Integer `≤`. -/
  | le (a b : Expr (.color .int)) : Expr (.color .bool)
  /-- Integer `<`. -/
  | lt (a b : Expr (.color .int)) : Expr (.color .bool)
  /-- Conjunction. -/
  | and (a b : Expr (.color .bool)) : Expr (.color .bool)
  /-- Disjunction. -/
  | or (a b : Expr (.color .bool)) : Expr (.color .bool)
  /-- Negation. -/
  | not (a : Expr (.color .bool)) : Expr (.color .bool)
  /-- The empty bag over `c`, the thesis's `∅_MS`. -/
  | emptyBag (c : Color) : Expr (.bag c)
  /-- The bag the thesis writes `{n`e}`. -/
  | single {c : Color} (n : Nat) (e : Expr (.color c)) : Expr (.bag c)
  /-- The union of two bags, operation 2. -/
  | bagUnion {c : Color} (a b : Expr (.bag c)) : Expr (.bag c)
  /-- The difference of two bags, operation 6. -/
  | bagDiff {c : Color} (a b : Expr (.bag c)) : Expr (.bag c)
  /-- The inclusion of one bag in another, operation 5. Translation-internal. -/
  | bagSubset {c : Color} (a b : Expr (.bag c)) : Expr (.color .bool)

/-- One expression per field of a record color, in declaration order. -/
inductive Args : ColorFields → Type where
  /-- No fields. -/
  | nil : Args .nil
  /-- One field, followed by the rest. -/
  | cons {n : String} {c : Color} {fs : ColorFields} (e : Expr (.color c)) (rest : Args fs) :
      Args (.cons n c fs)

end

namespace Expr

/-! ### Evaluation -/

mutual

/-- The value of an expression under a binding, written `e⟨b⟩` in the thesis. -/
def eval : {τ : ExprTy} → Expr τ → Env → τ.Denot
  | _, .var x τ, env => env τ x
  | _, .intLit n, _ => .int n
  | _, .boolLit b, _ => .bool b
  | _, .ctorLit _ _ id _, _ => .ctor id
  | _, .mkRec _ args, env => .record (Args.eval args env)
  | _, .proj e f c _, env => ((eval e env).asRecord.lookup f).getD c.junk
  | _, .add a b, env => .int ((eval a env).asInt + (eval b env).asInt)
  | _, .sub a b, env => .int ((eval a env).asInt - (eval b env).asInt)
  | _, .mul a b, env => .int ((eval a env).asInt * (eval b env).asInt)
  | _, .eq a b, env => .bool (eval a env == eval b env)
  | _, .le a b, env => .bool (decide ((eval a env).asInt ≤ (eval b env).asInt))
  | _, .lt a b, env => .bool (decide ((eval a env).asInt < (eval b env).asInt))
  | _, .and a b, env => .bool ((eval a env).asBool && (eval b env).asBool)
  | _, .or a b, env => .bool ((eval a env).asBool || (eval b env).asBool)
  | _, .not a, env => .bool (!(eval a env).asBool)
  | _, .emptyBag _, _ => ∅
  | _, .single n e, env => Bag.single n (eval e env)
  | _, .bagUnion a b, env => eval a env ∪ eval b env
  | _, .bagDiff a b, env => eval a env \ eval b env
  | _, .bagSubset a b, env => .bool (Bag.subsetB (eval a env) (eval b env))

/-- `Expr.eval`, one field at a time. -/
def Args.eval : {fs : ColorFields} → Args fs → Env → ValueFields
  | _, .nil, _ => .nil
  | _, @Args.cons n _ _ e rest, env => .cons n (eval e env) (Args.eval rest env)

end

/-- A boolean expression holds under a binding. This is `Type[e] = Bool` together with
`e⟨b⟩ = True`, as Definitions 6 and 14 use it. -/
def Holds (e : Expr (.color .bool)) (env : Env) : Prop := (eval e env).asBool = true

instance (e : Expr (.color .bool)) (env : Env) : Decidable (Holds e env) :=
  inferInstanceAs (Decidable (_ = true))

/-! ### Free variables

`VAR[e]` of Chapter 2. The list may repeat a variable; only membership is ever used. -/

mutual

/-- The variables occurring in an expression, with their sorts. -/
def freeVars : {τ : ExprTy} → Expr τ → Ctx
  | _, .var x τ => [(x, τ)]
  | _, .intLit _ => []
  | _, .boolLit _ => []
  | _, .ctorLit _ _ _ _ => []
  | _, .mkRec _ args => Args.freeVars args
  | _, .proj e _ _ _ => freeVars e
  | _, .add a b => freeVars a ++ freeVars b
  | _, .sub a b => freeVars a ++ freeVars b
  | _, .mul a b => freeVars a ++ freeVars b
  | _, .eq a b => freeVars a ++ freeVars b
  | _, .le a b => freeVars a ++ freeVars b
  | _, .lt a b => freeVars a ++ freeVars b
  | _, .and a b => freeVars a ++ freeVars b
  | _, .or a b => freeVars a ++ freeVars b
  | _, .not a => freeVars a
  | _, .emptyBag _ => []
  | _, .single _ e => freeVars e
  | _, .bagUnion a b => freeVars a ++ freeVars b
  | _, .bagDiff a b => freeVars a ++ freeVars b
  | _, .bagSubset a b => freeVars a ++ freeVars b

/-- `Expr.freeVars`, one field at a time. -/
def Args.freeVars : {fs : ColorFields} → Args fs → Ctx
  | _, .nil => []
  | _, .cons e rest => freeVars e ++ Args.freeVars rest

end

/-- An expression is scoped in `Γ` when every variable it mentions is a variable of `Γ` at the
sort `Γ` gives it.

This is check 7 of `Implementation/docs/InputFormat.md` §4.3, `Var(t) ⊆ V`, which
`Thesis/docs/LeanFormalization.md` §4.6 records as provable from the typing but not stated in
`Proof/`. Here it is neither: it is checked at the boundary and then used. -/
def ScopedIn (Γ : Ctx) {τ : ExprTy} (e : Expr τ) : Prop := ∀ p ∈ e.freeVars, p ∈ Γ

instance (Γ : Ctx) {τ : ExprTy} (e : Expr τ) : Decidable (ScopedIn Γ e) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- An expression scoped in `Γ` is scoped in anything larger. -/
theorem ScopedIn.mono {Γ Δ : Ctx} (hsub : ∀ p ∈ Γ, p ∈ Δ) {τ : ExprTy} {e : Expr τ}
    (h : ScopedIn Γ e) : ScopedIn Δ e :=
  fun p hp => hsub p (h p hp)

/-! ### Obligation 4: an expression sees only its free variables

`Implementation/docs/Plan.md` §4 obligation 4 asks for the lemma relating "`E(p,t)` evaluated
under a binding `b` of the transition" to "the translated term evaluated under `d ↦ M` and
`h ↦ b`". Because the translation moves an expression between contexts without changing it,
that lemma is exactly this congruence: the two environments agree on `Var(t)`, which contains
the free variables of `E(p,t)`, so the two evaluations agree.

`Thesis/docs/LeanFormalization.md` §5.1 calls this "the one genuinely new proof obligation".
`Cpn2mCrl2/Correct.lean` is where it is discharged; here it is proved. -/

mutual

/-- Two environments agreeing on the free variables of `e` give it the same value. -/
theorem eval_congr : ∀ {τ : ExprTy} (e : Expr τ) {env₁ env₂ : Env},
    (∀ p ∈ e.freeVars, env₁ p.2 p.1 = env₂ p.2 p.1) → eval e env₁ = eval e env₂
  | _, .var x τ, _, _, h => h (x, τ) (List.mem_singleton.2 rfl)
  | _, .intLit _, _, _, _ => rfl
  | _, .boolLit _, _, _, _ => rfl
  | _, .ctorLit _ _ _ _, _, _, _ => rfl
  | _, .mkRec _ args, _, _, h => by
      show Value.record _ = Value.record _
      rw [Args.eval_congr args h]
  | _, .proj e _ _ _, _, _, h => by
      show ((eval e _).asRecord.lookup _).getD _ = ((eval e _).asRecord.lookup _).getD _
      rw [eval_congr e h]
  | _, .add a b, _, _, h => by
      show Value.int _ = Value.int _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .sub a b, _, _, h => by
      show Value.int _ = Value.int _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .mul a b, _, _, h => by
      show Value.int _ = Value.int _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .eq a b, _, _, h => by
      show Value.bool _ = Value.bool _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .le a b, _, _, h => by
      show Value.bool _ = Value.bool _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .lt a b, _, _, h => by
      show Value.bool _ = Value.bool _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .and a b, _, _, h => by
      show Value.bool _ = Value.bool _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .or a b, _, _, h => by
      show Value.bool _ = Value.bool _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .not a, _, _, h => by
      show Value.bool _ = Value.bool _
      rw [eval_congr a h]
  | _, .emptyBag _, _, _, _ => rfl
  | _, .single n e, _, _, h => by
      show Bag.single n _ = Bag.single n _
      rw [eval_congr e h]
  | _, .bagUnion a b, _, _, h => by
      show _ ∪ _ = _ ∪ _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .bagDiff a b, _, _, h => by
      show _ \ _ = _ \ _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]
  | _, .bagSubset a b, _, _, h => by
      show Value.bool _ = Value.bool _
      rw [eval_congr a fun p hp => h p (List.mem_append_left _ hp),
        eval_congr b fun p hp => h p (List.mem_append_right _ hp)]

/-- `Expr.eval_congr`, one field at a time. -/
theorem Args.eval_congr : ∀ {fs : ColorFields} (args : Args fs) {env₁ env₂ : Env},
    (∀ p ∈ Args.freeVars args, env₁ p.2 p.1 = env₂ p.2 p.1) →
    Args.eval args env₁ = Args.eval args env₂
  | _, .nil, _, _, _ => rfl
  | _, .cons e rest, _, _, h => by
      show ValueFields.cons _ _ _ = ValueFields.cons _ _ _
      rw [eval_congr e fun p hp => h p (List.mem_append_left _ hp),
        Args.eval_congr rest fun p hp => h p (List.mem_append_right _ hp)]

end

/-- The form obligation 4 is used in: an expression scoped in `Γ` is evaluated the same by any
two environments that agree on `Γ`. -/
theorem eval_congr_of_scoped {Γ : Ctx} {τ : ExprTy} {e : Expr τ} (hs : ScopedIn Γ e)
    {env₁ env₂ : Env} (h : ∀ p ∈ Γ, env₁ p.2 p.1 = env₂ p.2 p.1) :
    eval e env₁ = eval e env₂ :=
  eval_congr e fun p hp => h p (hs p hp)

/-- The conjunction of a list of boolean expressions, which is how the bounded `∀ p ∈ pre(t)`
of Definition 14 is emitted: obligation 3 of `Implementation/docs/Plan.md` §4 unfolds it at
translation time, so the data language needs no quantifier. -/
def andAll : List (Expr (.color .bool)) → Expr (.color .bool)
  | [] => .boolLit true
  | [e] => e
  | e :: es => .and e (andAll es)

/-- `andAll` holds exactly when every conjunct does. -/
theorem holds_andAll {es : List (Expr (.color .bool))} {env : Env} :
    Holds (andAll es) env ↔ ∀ e ∈ es, Holds e env := by
  induction es with
  | nil => simp [andAll, Holds, eval, Value.asBool]
  | cons hd tl ih =>
    cases tl with
    | nil => simp [andAll, Holds]
    | cons hd' tl' =>
      simp only [andAll, Holds, eval, Value.asBool, Bool.and_eq_true, List.mem_cons] at *
      constructor
      · rintro ⟨h₁, h₂⟩ e (rfl | he)
        · exact h₁
        · exact ih.1 h₂ e he
      · intro h
        exact ⟨h hd (Or.inl rfl), ih.2 fun e he => h e (Or.inr he)⟩

/-- The union of a list of bag expressions. -/
def unionAll {c : Color} : List (Expr (.bag c)) → Expr (.bag c)
  | [] => .emptyBag c
  | [e] => e
  | e :: es => .bagUnion e (unionAll es)

end Expr

end Cpn2mCrl2
