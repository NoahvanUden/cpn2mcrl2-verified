/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2
import Proof.Soundness

/-!
# The concrete language as an `ExprLang`

`Proof/CommonDefinitions.lean` leaves the expression language abstract, as Chapter 2 of the
thesis does, and packages the assumptions as a structure:

> `ExprLang` below packages exactly those assumptions, so that everything downstream is stated for an arbitrary expression language rather than for one particular choice.

`Implementation/docs/Plan.md` §3 says a program cannot do that and has to commit, and
`Cpn2mCrl2/Expr.lean` commits. This file is the reconciliation: the concrete language *is* one
of the languages `Proof/` quantifies over, so everything `Proof/` proves applies to it.

## The four choices that need care

**Values are a subtype.** `ExprLang.val` has to satisfy `val boolColor ≃ Bool`, so it cannot be
all of `Value`. It is `{v : Value // v.ofColor c = true}` -- the values *of* the color -- which
is why `Cpn2mCrl2/Typing.lean` had to exist before this file could: producing the `ExprLang`'s
`eval` at all needs the proof that evaluation preserves sorts.

**Expressions are a subtype too.** `L.Expr τ` is every expression of that sort, and `eval` has
to be total on it. An expression mentioning a variable at a color other than the one `V` gives
it has no meaning under a binding of `V`, so `L.Expr` is restricted to the expressions scoped
in `N.vars`. Everything a CPN carries is scoped, by `Net.Valid`.

**`varType` is read off the net.** `ExprLang.varType` is a total function `Var → Color`, while
a net's `V` is a finite list. `Net.varTypeOf` is the lookup, defaulting to `Bool` off `V`;
`Net.varTypeOf_of_mem` is the only fact about it anything uses.

**The language depends on the net, and on its validity.** `ExprLang` is a structure of data,
and the data here needs `Net.Valid` to be well-defined -- the `eval` field cannot be built
without knowing that variables are color-sorted and typed by `V`. Proof irrelevance makes that
harmless: `Net.lang N h₁` and `Net.lang N h₂` are the same language.

## Main definitions

* `Cpn2mCrl2.Net.lang` : the `ExprLang` of a valid net.
* `Cpn2mCrl2.Bridge.envOfBinding` : a `Bindings` of `Proof/` read as a `Cpn2mCrl2.Env`.
-/

universe u

namespace Cpn2mCrl2

open Cpn2mCrl2 (Color Value)

/-! ## Reading a list by key

Definition 5 makes `C`, `I`, `Type[.]` and `E` functions; here they are lists, so each is a
lookup, and that the lookup finds the right entry is where the distinctness conditions of
`Net.Valid` do their work. `Cpn2mCrl2/Correct.lean` proves the same three facts for places;
these are the versions for variables and for arcs. -/

namespace Bridge

theorem lookup_of_mem {β : Type} :
    ∀ {l : List (String × β)}, ListUtil.NoDup (l.map Prod.fst) →
      ∀ {p : String × β}, p ∈ l → List.lookup p.1 l = some p.2 := by
  intro l
  induction l with
  | nil => intro _ p hp; cases hp
  | cons e tl ih =>
    intro hnd p hp
    by_cases he : e.1 = p.1
    · have hep : e = p := by
        rcases List.mem_cons.1 hp with hq | hq
        · exact hq.symm
        · exact absurd (he ▸ List.mem_map_of_mem (f := Prod.fst) hq) hnd.1
      have hbeq : (p.1 == e.1) = true := by simp [he]
      rw [List.lookup_cons, hbeq, hep]
    · have hpt : p ∈ tl := by
        rcases List.mem_cons.1 hp with hq | hq
        · exact absurd (congrArg Prod.fst hq.symm) he
        · exact hq
      have hne : p.1 ≠ e.1 := fun hq => he hq.symm
      have hbeq : (p.1 == e.1) = false := by simp [hne]
      rw [List.lookup_cons, hbeq]
      exact ih hnd.2 hpt

theorem find?_arc_of_mem :
    ∀ {l : List ArcDecl}, ListUtil.NoDup (l.map fun x : ArcDecl => (x.place, x.transition)) →
      ∀ {a : ArcDecl}, a ∈ l →
        l.find? (fun x => x.place == a.place && x.transition == a.transition) = some a := by
  intro l
  induction l with
  | nil => intro _ a ha; cases ha
  | cons e tl ih =>
    intro hnd a ha
    by_cases he : e.place = a.place ∧ e.transition = a.transition
    · have hea : e = a := by
        rcases List.mem_cons.1 ha with hq | hq
        · exact hq.symm
        · exfalso
          apply hnd.1
          show (e.place, e.transition) ∈ tl.map fun x : ArcDecl => (x.place, x.transition)
          rw [he.1, he.2]
          exact List.mem_map_of_mem hq
      exact (List.find?_cons_of_pos (by simp [he.1, he.2])).trans (by rw [hea])
    · have hat : a ∈ tl := by
        rcases List.mem_cons.1 ha with hq | hq
        · exact absurd (And.intro (congrArg ArcDecl.place hq.symm)
            (congrArg ArcDecl.transition hq.symm)) he
        · exact hq
      have hne : ¬((e.place == a.place && e.transition == a.transition) = true) := by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact he
      exact (List.find?_cons_of_neg
        (p := fun x : ArcDecl => x.place == a.place && x.transition == a.transition)
        hne).trans (ih hnd.2 hat)

end Bridge

namespace Net

/-- `Type[.]` as a total function, which is what `ExprLang.varType` has to be. Off `V` the
value is irrelevant and `Bool` -- which Definition 5 requires every net to declare -- is as
good as any. -/
def varTypeOf (N : Net) (x : String) : Color :=
  match List.lookup x N.vars with
  | some τ => τ.color!
  | none => .bool

theorem varTypeOf_of_mem {N : Net} (h : N.Valid) {x : String} {τ : ExprTy}
    (hx : (x, τ) ∈ N.vars) : τ = .color (N.varTypeOf x) := by
  have hl : List.lookup x N.vars = some τ := Bridge.lookup_of_mem h.varsNodup hx
  have hc : τ.isColor = true := h.varsAreColors _ hx
  rw [varTypeOf, hl]
  exact ExprTy.eq_color_of_isColor hc

theorem mem_varNames_of_mem {N : Net} {x : String} {τ : ExprTy} (hx : (x, τ) ∈ N.vars) :
    x ∈ N.varNames :=
  List.mem_map_of_mem (f := Prod.fst) hx

end Net

namespace Bridge

/-! ## The values of a color -/

/-- The values of the color `c`: what `ExprLang.val` has to be, given that it must satisfy
`val boolColor ≃ Bool`. -/
def Val (c : Color) : Type := {v : Value // v.ofColor c = true}

/-- The values of `Bool` are the booleans, which is Definition 5's requirement that `Σ`
contain `Bool` with its intended meaning. -/
def boolEquiv : Val .bool ≃ Bool where
  toFun v := v.1.asBool
  invFun b := ⟨.bool b, rfl⟩
  left_inv := by
    rintro ⟨v, hv⟩
    refine Subtype.ext ?_
    cases v with
    | bool b => rfl
    | int _ => exact absurd hv (by simp [Value.ofColor])
    | ctor _ => exact absurd hv (by simp [Value.ofColor])
    | record _ => exact absurd hv (by simp [Value.ofColor])
  right_inv _ := rfl

/-! ## Sorts -/

/-- `Proof/`'s `ExprTy` read as ours. The two are the same two constructors over the same
colors; they are different inductives only because one lives in `Proof/` and one here. -/
def ofPTy : _root_.ExprTy Color → ExprTy
  | .color c => .color c
  | .bag c => .bag c

@[simp] theorem ofPTy_color (c : Color) : ofPTy (.color c) = .color c := rfl

@[simp] theorem ofPTy_bag (c : Color) : ofPTy (.bag c) = .bag c := rfl

/-! ## Bindings -/

open Classical in
/-- A binding of `Proof/`, read as one of ours: a variable of `V` gets the value the binding
gives it, everything else gets junk that nothing will look at.

`Expr.eval_congr` -- obligation 4 of `Implementation/docs/Plan.md` §4 -- is what makes the junk
harmless: an expression scoped in `V` cannot see it.

`V` is a `Set`, so membership is not decidable and the definition is classical and
noncomputable. That is proper: nothing in this directory runs, and the translator that does
never builds one of these. -/
noncomputable def envOfBinding (N : Net) (V : Set String) (b : Bindings Val N.varTypeOf V) :
    Env
  | .color c, x => if h : x ∈ V then (b ⟨x, h⟩).1 else c.junk
  | .bag _, _ => ∅

theorem envOfBinding_color {N : Net} {V : Set String} (b : Bindings Val N.varTypeOf V)
    {x : String} (hx : x ∈ V) (c : Color) :
    envOfBinding N V b (.color c) x = (b ⟨x, hx⟩).1 := by
  classical
  show (if h : x ∈ V then (b ⟨x, h⟩).1 else c.junk) = _
  rw [dite_eq_left hx]

/-- The environment a binding of `V` gives is well-typed on every part of `V` that a net's own
variables cover, which is what `Expr.eval_wf` needs. -/
theorem wfOn_envOfBinding {N : Net} (h : N.Valid) {V : Set String}
    (b : Bindings Val N.varTypeOf V) {Γ : Ctx} (hΓ : ∀ p ∈ Γ, p ∈ N.vars)
    (hV : ∀ p ∈ Γ, p.1 ∈ V) : (envOfBinding N V b).WfOn Γ := by
  rintro ⟨x, τ⟩ hp
  have hmem := hΓ _ hp
  have hτ : τ = .color (N.varTypeOf x) := Net.varTypeOf_of_mem h hmem
  subst hτ
  rw [envOfBinding_color b (hV _ hp)]
  exact (b ⟨x, hV _ hp⟩).2

end Bridge

/-! ## The language -/

namespace Net

/-- The expressions of the language: those of the right sort that are scoped in `V`.

The restriction is what makes `eval` total. It costs nothing, because every expression a CPN
carries is scoped in `V` -- that is `Net.Valid.guardScoped`, `inArcScoped` and `outArcScoped`,
which are check 7 of `Implementation/docs/InputFormat.md` §4.3. -/
def LangExpr (N : Net) (τ : _root_.ExprTy Color) : Type :=
  {e : Expr (Bridge.ofPTy τ) // Expr.ScopedIn N.vars e}

/-- The free variables of such an expression, as `ExprLang.vars` wants them: a set of
names. -/
def langVars (N : Net) {τ : _root_.ExprTy Color} (e : N.LangExpr τ) : Set String :=
  {x | ∃ σ, (x, σ) ∈ e.1.freeVars}

theorem mem_langVars (N : Net) {τ : _root_.ExprTy Color} {e : N.LangExpr τ} {x : String}
    {σ : ExprTy} (hx : (x, σ) ∈ e.1.freeVars) : x ∈ N.langVars e := ⟨σ, hx⟩

theorem langVars_subset_varNames (N : Net) {τ : _root_.ExprTy Color} (e : N.LangExpr τ) :
    N.langVars e ⊆ {x | x ∈ N.varNames} := by
  rintro x ⟨σ, hσ⟩
  exact Net.mem_varNames_of_mem (e.2 _ hσ)

/-- The environment in which such an expression is evaluated, from a binding of its free
variables. -/
noncomputable def langEnv (N : Net) {τ : _root_.ExprTy Color} (e : N.LangExpr τ)
    (b : Bindings Bridge.Val N.varTypeOf (N.langVars e)) : Env :=
  Bridge.envOfBinding N (N.langVars e) b

theorem wfOn_langEnv {N : Net} (h : N.Valid) {τ : _root_.ExprTy Color} (e : N.LangExpr τ)
    (b : Bindings Bridge.Val N.varTypeOf (N.langVars e)) :
    (N.langEnv e b).WfOn e.1.freeVars :=
  Bridge.wfOn_envOfBinding h b (fun q hq => e.2 q hq) (fun _ hq => N.mem_langVars hq)

/-- The evaluation of the language: ours, with the result read at the sort `Proof/` expects --
a value of the color, or a coefficient function on those values. -/
noncomputable def langEval (N : Net) (h : N.Valid) :
    ∀ (τ : _root_.ExprTy Color) (e : N.LangExpr τ),
      Bindings Bridge.Val N.varTypeOf (N.langVars e) → τ.Value Bridge.Val
  | .color _, e, b => ⟨Expr.eval e.1 (N.langEnv e b), Expr.eval_wf e.1 (wfOn_langEnv h e b)⟩
  | .bag _, e, b => fun v => (Expr.eval e.1 (N.langEnv e b)).coeff v.1

/-- **The concrete language, as one of the languages `Proof/` quantifies over.** -/
noncomputable def lang (N : Net) (h : N.Valid) : ExprLang where
  Color := Color
  val := Bridge.Val
  boolColor := .bool
  boolVal := Bridge.boolEquiv
  Var := String
  varType := N.varTypeOf
  Expr := N.LangExpr
  vars := N.langVars
  eval := fun {τ} e b => N.langEval h τ e b

@[simp] theorem lang_Color (N : Net) (h : N.Valid) : (N.lang h).Color = Color := rfl

@[simp] theorem lang_val (N : Net) (h : N.Valid) : (N.lang h).val = Bridge.Val := rfl

@[simp] theorem lang_Var (N : Net) (h : N.Valid) : (N.lang h).Var = String := rfl

@[simp] theorem lang_varType (N : Net) (h : N.Valid) : (N.lang h).varType = N.varTypeOf := rfl

@[simp] theorem lang_vars (N : Net) (h : N.Valid) {τ : _root_.ExprTy Color}
    (e : N.LangExpr τ) : (N.lang h).vars e = N.langVars e := rfl

/-- Evaluation at a color sort is ours, wrapped. -/
theorem lang_eval_color (N : Net) (h : N.Valid) {c : Color} (e : N.LangExpr (.color c))
    (b : Bindings Bridge.Val N.varTypeOf (N.langVars e)) :
    ((N.lang h).eval e b).1 = Expr.eval e.1 (N.langEnv e b) := rfl

/-- Evaluation at a bag sort is the coefficient function of ours. -/
theorem lang_eval_bag (N : Net) (h : N.Valid) {c : Color} (e : N.LangExpr (.bag c))
    (b : Bindings Bridge.Val N.varTypeOf (N.langVars e)) (v : Bridge.Val c) :
    (N.lang h).eval e b v = (Expr.eval e.1 (N.langEnv e b)).coeff v.1 := rfl

end Net

end Cpn2mCrl2
