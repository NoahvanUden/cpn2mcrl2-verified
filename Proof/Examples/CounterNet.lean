/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Proof.ColoredPetriNets

/-!
# Examples 3 and 4: a counter net

The CPN of Example 3 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025), Chapter 3, together with the enabledness and occurrence computed
in Example 4. See `Thesis/docs/ColoredPetriNets.md` for the prose version.

In the net: the initial marking of `p₁` holds a token with value 1; `t₁` moves it to `p₂`
incremented by one; while the value is at most three `t₂` moves it back to `p₁` unchanged;
once it is greater than three `t₃` moves it to `p₃` unchanged.

Not every annotation of this net is printed in the thesis. The table in Example 3 of the
notes gives `I(P₁)`, `C`, `E(P₁, T₁)`, `E(T₁, P₂)`, `G(T₂)` and `G(T₃)`. The rest is read
off the text: the remaining arc expressions from "consumes a token from `p₂` and produces a
token in `p₁` with the same value", `I(P₂)` and `I(P₃)` from `p₁` being the only place
holding a token initially, and `G(T₁) = True` from the computation
`G(t₁)⟨n = 1⟩ = True⟨n = 1⟩ = True` in Example 4.
-/
namespace CounterNet

/-- The colors of the net: `INT` and, as required of every CPN, `Bool`. -/
inductive Color | int | bool
  deriving DecidableEq

/-- The values of each color. -/
abbrev val : Color → Type
  | .int => ℤ
  | .bool => Bool

/-- The variables: only `n` occurs in this net. -/
inductive Var | n
  deriving DecidableEq

/-- `n` is an integer variable. -/
abbrev varType : Var → Color
  | .n => .int

/-- An expression, modelled by its free variables together with the function that evaluates
it under a binding of those variables. -/
structure Expr (τ : ExprTy Color) where
  /-- The free variables of the expression. -/
  vars : Set Var
  /-- The value of the expression under a binding of its free variables. -/
  eval : Bindings val varType vars → τ.Value val

/-- The expression language of Example 3. -/
def lang : ExprLang where
  Color := Color
  val := val
  boolColor := .bool
  boolVal := Equiv.refl Bool
  Var := Var
  varType := varType
  Expr := Expr
  vars e := e.vars
  eval e b := e.eval b

/-- The value the binding `b` gives to `n`. -/
def valueOfN {V : Set Var} (h : Var.n ∈ V) (b : Bindings val varType V) : ℤ := b ⟨.n, h⟩

/-- The only free variable used in this net. -/
def onlyN : Set Var := {Var.n}

theorem n_mem_onlyN : Var.n ∈ onlyN := rfl

/-- The arc expression `{1`n}`, a single token carrying the value of `n`. -/
def tokenN : Expr (.bag .int) where
  vars := onlyN
  eval b := Bag.single 1 (valueOfN n_mem_onlyN b)

/-- The arc expression `{1`(n+1)}`. -/
def tokenNSucc : Expr (.bag .int) where
  vars := onlyN
  eval b := Bag.single 1 (valueOfN n_mem_onlyN b + 1)

/-- The guard `True`. -/
def guardTrue : Expr (.color .bool) where
  vars := ∅
  eval _ := true

/-- The guard `n ≤ 3`. -/
def guardLe : Expr (.color .bool) where
  vars := onlyN
  eval b := decide (valueOfN n_mem_onlyN b ≤ 3)

/-- The guard `n > 3`. -/
def guardGt : Expr (.color .bool) where
  vars := onlyN
  eval b := decide (3 < valueOfN n_mem_onlyN b)

/-- The initialization expression `{1`1}` of `p₁`. -/
def initToken : Expr (.bag .int) where
  vars := ∅
  eval _ := Bag.single 1 (1 : ℤ)

/-- The initialization expression of the places that start out empty. -/
def initEmpty : Expr (.bag .int) where
  vars := ∅
  eval _ := ∅

/-- The three places of Example 3. -/
inductive Place | p₁ | p₂ | p₃
  deriving DecidableEq

/-- The three transitions of Example 3. -/
inductive Trans | t₁ | t₂ | t₃
  deriving DecidableEq

instance : Fintype Place := ⟨{.p₁, .p₂, .p₃}, fun x => by cases x <;> decide⟩

instance : Fintype Trans := ⟨{.t₁, .t₂, .t₃}, fun x => by cases x <;> decide⟩

/-- The CPN of Example 3. -/
def net : CPN lang Place Trans where
  finitePlaces := Finite.of_fintype _
  finiteTransitions := Finite.of_fintype _
  inArc := {(.p₁, .t₁), (.p₂, .t₂), (.p₂, .t₃)}
  outArc := {(.t₁, .p₂), (.t₂, .p₁), (.t₃, .p₃)}
  colors := {.int, .bool}
  finiteColors := (Set.finite_singleton _).insert _
  boolMem := Or.inr rfl
  V := onlyN
  finiteV := Set.finite_singleton _
  varTypeMem := by rintro _ rfl; exact Or.inl rfl
  C _ := .int
  colorMem _ := Or.inl rfl
  G t := match t with
    | .t₁ => ⟨guardTrue, Set.empty_subset _⟩
    | .t₂ => ⟨guardLe, subset_rfl⟩
    | .t₃ => ⟨guardGt, subset_rfl⟩
  Ein _ _ := ⟨tokenN, subset_rfl⟩
  Eout a _ := match a.1 with
    | .t₁ => ⟨tokenNSucc, subset_rfl⟩
    | _ => ⟨tokenN, subset_rfl⟩
  I p := match p with
    | .p₁ => ⟨initToken, Set.empty_subset _⟩
    | _ => ⟨initEmpty, Set.empty_subset _⟩

theorem initialMarking_p₁ : net.initialMarking .p₁ = Bag.single 1 (1 : ℤ) := rfl

theorem initialMarking_p₂ : net.initialMarking .p₂ = ∅ := rfl

/-! ## Example 4

The binding `⟨n = 1⟩` makes `(t₁, ⟨n = 1⟩)` enabled in the initial marking, and its
occurrence empties `p₁` and puts the token `{1`2}` in `p₂`. -/

/-- The binding `⟨n = 1⟩` of `t₁`. -/
def bindOne : net.TransBinding .t₁ := fun v =>
  match v.1 with
  | .n => (1 : ℤ)

theorem enabled_t₁ : CPN.Enabled net.initialMarking bindOne := by
  refine ⟨?_, rfl⟩
  rintro (_ | _ | _) h
  -- `p₁` is the only place in the preset of `t₁`, and it holds exactly the token
  -- `E(p₁, t₁)⟨n = 1⟩ = {1`1}` that `t₁` consumes from it.
  · exact fun _ => Nat.le_refl _
  · simp [net, CPN.pre] at h
  · simp [net, CPN.pre] at h

/-- `E(p₁, t₁)⟨n = 1⟩ = {1`1}`, as computed in Example 4. -/
theorem consumed_t₁_p₁ (h : (Place.p₁, Trans.t₁) ∈ net.inArc) :
    CPN.consumedBy bindOne .p₁ h = Bag.single 1 (1 : ℤ) := rfl

/-- `E(t₁, p₂)⟨n = 1⟩ = {1`(1+1)} = {1`2}`, as computed in Example 4. -/
theorem produced_t₁_p₂ (h : (Trans.t₁, Place.p₂) ∈ net.outArc) :
    CPN.producedBy bindOne .p₂ h = Bag.single 1 (2 : ℤ) := rfl

/-- After `(t₁, ⟨n = 1⟩)` has occurred, `p₁` is empty: the token it held is consumed, and
nothing is produced there. -/
theorem fire_t₁_p₁ : CPN.fire net.initialMarking bindOne .p₁ = ∅ := by
  have hin : (Place.p₁, Trans.t₁) ∈ net.inArc := by simp [net]
  have hout : (Trans.t₁, Place.p₁) ∉ net.outArc := by simp [net]
  ext s
  simp only [CPN.fire, initialMarking_p₁, CPN.consume, hin, ↓reduceDIte, consumed_t₁_p₁,
    CPN.produce, hout, Bag.union_apply, Bag.empty_apply, add_zero]
  exact Nat.sub_self _

/-- ... and `p₂` holds the token `{1`2}`. -/
theorem fire_t₁_p₂ : CPN.fire net.initialMarking bindOne .p₂ = Bag.single 1 (2 : ℤ) := by
  have hin : (Place.p₂, Trans.t₁) ∉ net.inArc := by simp [net]
  have hout : (Trans.t₁, Place.p₂) ∈ net.outArc := by simp [net]
  ext s
  simp only [CPN.fire, initialMarking_p₂, CPN.consume, hin, ↓reduceDIte, CPN.produce, hout,
    produced_t₁_p₂]
  exact Nat.zero_add _

/-- The place `p₃` is not connected to `t₁`, so it keeps its marking. -/
theorem fire_t₁_p₃ : CPN.fire net.initialMarking bindOne .p₃ = net.initialMarking .p₃ :=
  CPN.fire_of_not_mem _ _ (by simp [net]) (by simp [net])

/-! ## Definitions 6 and 7 in closed form

Example 4 computes one binding element in one marking. The following say, for an arbitrary
marking and an arbitrary binding, exactly which binding elements of this net are enabled and
exactly which marking each one leads to. Example 9 (`Examples/CounterNetLPE.lean`) and
Example 5 (`Examples/CounterNetGraph.lean`) are both read off these. -/

/-- `n` is a variable of each of the three transitions: of `t₁` because it occurs in the arc
expression on `(p₁, t₁)`, and of `t₂` and `t₃` because it occurs in their guards. -/
theorem n_mem_var : ∀ t : Trans, Var.n ∈ net.Var t
  | .t₁ => net.vars_Ein_subset (p := .p₁) (t := .t₁) (by simp [net]) rfl
  | .t₂ => net.vars_G_subset .t₂ rfl
  | .t₃ => net.vars_G_subset .t₃ rfl

/-- The integer a binding of a transition gives to `n`: the `h` summed over in Example 9. -/
def valueOf {t : Trans} (b : net.TransBinding t) : ℤ := b ⟨.n, n_mem_var t⟩

/-- Every place of this net is `INT`-colored, so the tokens in a place are integers; this
lets `Bag.single` be written for them. -/
instance decEqTokens (p : Place) : DecidableEq (lang.val (net.C p)) :=
  inferInstanceAs (DecidableEq ℤ)

/-- A marking of this net, given as the bags of tokens of its three places. -/
def marking (a b c : Bag ℤ) : net.Marking := fun p =>
  match p with
  | .p₁ => a
  | .p₂ => b
  | .p₃ => c

@[simp] theorem marking_p₁ (a b c : Bag ℤ) : marking a b c .p₁ = a := rfl

@[simp] theorem marking_p₂ (a b c : Bag ℤ) : marking a b c .p₂ = b := rfl

@[simp] theorem marking_p₃ (a b c : Bag ℤ) : marking a b c .p₃ = c := rfl

/-- The initial marking `M₀ = ({1`1}, ∅, ∅)`. -/
theorem initialMarking_eq : net.initialMarking = marking (Bag.single 1 (1 : ℤ)) ∅ ∅ := by
  funext p; cases p <;> rfl

/-! ### Enabledness

`pre(t₁) = {p₁}` and `G(t₁) = True`; `pre(t₂) = pre(t₃) = {p₂}`, with the guards `n ≤ 3` and
`n > 3`. -/

theorem enabled_t₁_iff (M : net.Marking) (b : net.TransBinding .t₁) :
    CPN.Enabled M b ↔ Bag.single 1 (valueOf b) ⊆ M .p₁ := by
  constructor
  · rintro ⟨harcs, -⟩
    exact harcs .p₁ (by simp [net, CPN.pre])
  · intro hbag
    refine ⟨?_, rfl⟩
    rintro (_ | _ | _) hp
    · exact hbag
    · simp [net, CPN.pre] at hp
    · simp [net, CPN.pre] at hp

theorem enabled_t₂_iff (M : net.Marking) (b : net.TransBinding .t₂) :
    CPN.Enabled M b ↔ Bag.single 1 (valueOf b) ⊆ M .p₂ ∧ valueOf b ≤ 3 := by
  constructor
  · rintro ⟨harcs, hguard⟩
    exact ⟨harcs .p₂ (by simp [net, CPN.pre]), of_decide_eq_true hguard⟩
  · rintro ⟨hbag, hle⟩
    refine ⟨?_, decide_eq_true hle⟩
    rintro (_ | _ | _) hp
    · simp [net, CPN.pre] at hp
    · exact hbag
    · simp [net, CPN.pre] at hp

theorem enabled_t₃_iff (M : net.Marking) (b : net.TransBinding .t₃) :
    CPN.Enabled M b ↔ Bag.single 1 (valueOf b) ⊆ M .p₂ ∧ 3 < valueOf b := by
  constructor
  · rintro ⟨harcs, hguard⟩
    exact ⟨harcs .p₂ (by simp [net, CPN.pre]), of_decide_eq_true hguard⟩
  · rintro ⟨hbag, hgt⟩
    refine ⟨?_, decide_eq_true hgt⟩
    rintro (_ | _ | _) hp
    · simp [net, CPN.pre] at hp
    · exact hbag
    · simp [net, CPN.pre] at hp

/-! ### Occurrence

`t₁` moves the token from `p₁` to `p₂` incremented by one, `t₂` moves it from `p₂` back to
`p₁` unchanged, and `t₃` moves it from `p₂` to `p₃` unchanged. The place each transition is
not connected to keeps its marking, by the convention on arc expressions of non-existing
arcs. -/

theorem fire_t₁ (M : net.Marking) (b : net.TransBinding .t₁) :
    CPN.fire M b
      = marking (M .p₁ \ Bag.single 1 (valueOf b))
          (M .p₂ ∪ Bag.single 1 (valueOf b + 1)) (M .p₃) := by
  funext p
  cases p
  · have hin : (Place.p₁, Trans.t₁) ∈ net.inArc := by simp [net]
    have hout : (Trans.t₁, Place.p₁) ∉ net.outArc := by simp [net]
    ext s
    simp only [CPN.fire, CPN.consume, hin, ↓reduceDIte, CPN.produce, hout,
      Bag.union_apply, Bag.empty_apply, add_zero]
    rfl
  · have hin : (Place.p₂, Trans.t₁) ∉ net.inArc := by simp [net]
    have hout : (Trans.t₁, Place.p₂) ∈ net.outArc := by simp [net]
    ext s
    simp only [CPN.fire, CPN.consume, hin, ↓reduceDIte, CPN.produce, hout,
      Bag.union_apply, Bag.sdiff_apply, Bag.empty_apply, Nat.sub_zero]
    rfl
  · exact CPN.fire_of_not_mem _ _ (by simp [net]) (by simp [net])

theorem fire_t₂ (M : net.Marking) (b : net.TransBinding .t₂) :
    CPN.fire M b
      = marking (M .p₁ ∪ Bag.single 1 (valueOf b))
          (M .p₂ \ Bag.single 1 (valueOf b)) (M .p₃) := by
  funext p
  cases p
  · have hin : (Place.p₁, Trans.t₂) ∉ net.inArc := by simp [net]
    have hout : (Trans.t₂, Place.p₁) ∈ net.outArc := by simp [net]
    ext s
    simp only [CPN.fire, CPN.consume, hin, ↓reduceDIte, CPN.produce, hout,
      Bag.union_apply, Bag.sdiff_apply, Bag.empty_apply, Nat.sub_zero]
    rfl
  · have hin : (Place.p₂, Trans.t₂) ∈ net.inArc := by simp [net]
    have hout : (Trans.t₂, Place.p₂) ∉ net.outArc := by simp [net]
    ext s
    simp only [CPN.fire, CPN.consume, hin, ↓reduceDIte, CPN.produce, hout,
      Bag.union_apply, Bag.empty_apply, add_zero]
    rfl
  · exact CPN.fire_of_not_mem _ _ (by simp [net]) (by simp [net])

theorem fire_t₃ (M : net.Marking) (b : net.TransBinding .t₃) :
    CPN.fire M b
      = marking (M .p₁) (M .p₂ \ Bag.single 1 (valueOf b))
          (M .p₃ ∪ Bag.single 1 (valueOf b)) := by
  funext p
  cases p
  · exact CPN.fire_of_not_mem _ _ (by simp [net]) (by simp [net])
  · have hin : (Place.p₂, Trans.t₃) ∈ net.inArc := by simp [net]
    have hout : (Trans.t₃, Place.p₂) ∉ net.outArc := by simp [net]
    ext s
    simp only [CPN.fire, CPN.consume, hin, ↓reduceDIte, CPN.produce, hout,
      Bag.union_apply, Bag.empty_apply, add_zero]
    rfl
  · have hin : (Place.p₃, Trans.t₃) ∉ net.inArc := by simp [net]
    have hout : (Trans.t₃, Place.p₃) ∈ net.outArc := by simp [net]
    ext s
    simp only [CPN.fire, CPN.consume, hin, ↓reduceDIte, CPN.produce, hout,
      Bag.union_apply, Bag.sdiff_apply, Bag.empty_apply, Nat.sub_zero]
    rfl

end CounterNet
