/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Correct

/-!
# The list backend, and the refinement it needs

Milestone M6 of `Implementation/docs/Plan.md`. `Thesis/docs/mCRL2.md` §4.1 measures a
sevenfold speedup for storing a marking as a `List` rather than a `Bag`, and the reference
generator of `Implementation/docs/Target.md` §3 takes it. `Plan.md` §5 says what that costs:

> That is a sevenfold speedup, and it is also a departure from the object Theorem 1 is about. Two refinements separate them.

The two are **order** and **typing**. This file settles both.

## Order

A list-encoded marking is a *representative* of a bag, and two orders of production give two
distinct list states with the same underlying bag. `Plan.md` §5:

> Those states should be bisimilar, but they are not equal — so the induced LTS has strictly more states than the reachability graph, and bisimilarity holds where isomorphism fails. That is a provable lemma. Nobody has proved it.

`Net.listRel` is the relation "these two markings represent the same bags", and
`Net.step_of_toLpeList_step` and `Net.toLpeList_step_of_step` are its two halves: a step of
either encoding is matched by a step of the other. Nothing anywhere asks two list states to be
equal, which is exactly why the order does not matter.

## Typing

> A single tagged-union `token` sort shared by every place discards that, so nothing in the emitted specification prevents a place from holding a token of the wrong tag. Either the translation preserves a well-typedness invariant — provable, and worth proving — or the guarantee is simply weaker than Definition 5's.

Neither, here: this backend emits `List(C(p))`, one list sort per place at that place's *own*
color, so the invariant is the sort of the parameter and there is nothing to preserve. The
tagged union is the reference generator's choice and it is the choice that loses the guarantee;
`Thesis/docs/mCRL2.md` §4.1 attributes the speedup to `List` versus `Bag` and says nothing
about sharing a sort, so nothing is given up by not copying it.

## What is duplicated, and why

`ListLpe` repeats the shape of `Lpe` with list terms in place of bag terms rather than
generalizing it. `Lpe` and everything proved about it -- `Cpn2mCrl2/Correct.lean`, and the
bridge to Theorem 1 -- is settled; a second structure costs forty lines and risks nothing,
where making the first one polymorphic in the state sort would reopen all of it.

## Main results

* `Net.toLpeList` : the list-encoded LPE.
* `Net.holds_listCondTerm`, `Net.countOf_listNextMarking` : the condition and the next state
  against the bag encoding's.
* `Net.step_of_toLpeList_step`, `Net.toLpeList_step_of_step` : the refinement, as the two
  halves of a bisimulation. `Implementation/Lean/Bridge` packages them as one.
-/

namespace Cpn2mCrl2

/-! ## A bag term as a list term -/

/-- `n` copies of `e`, as a list term. -/
def Expr.replicateT {c : Color} : Nat → Expr (.color c) → Expr (.list c)
  | 0, _ => .nilList c
  | n + 1, e => .snoc (replicateT n e) e

theorem Expr.countOf_eval_replicateT {c : Color} (n : Nat) (e : Expr (.color c)) (env : Env)
    (w : Value) :
    countOf (Expr.eval (replicateT n e) env) w = if Expr.eval e env = w then n else 0 := by
  induction n with
  | zero => simp [replicateT, Expr.eval]
  | succ n ih =>
    show countOf (Expr.eval (replicateT n e) env ++ [Expr.eval e env]) w = _
    rw [countOf_append, ih]
    by_cases hw : Expr.eval e env = w
    · subst hw
      simp
    · simp [hw, countOf_cons_of_ne hw]

/-- A bag term as the list term denoting one of its representatives.

Total, but only meaningful on the bag terms a CPN carries: a bag-*sorted variable* is a place
parameter of the bag encoding, and translating it to a list-sorted variable of the same name is
right only because the list encoding names its parameters the same way. `Net.coeff_bagToList`
therefore assumes the term has no bag-sorted free variables, which
`Net.Valid.varsAreColors` gives for everything a CPN carries. -/
def Expr.bagToList : {c : Color} → Expr (.bag c) → Expr (.list c)
  | c, .var x (.bag _) => .var x (.list c)
  | c, .emptyBag _ => .nilList c
  | _, .single n e => replicateT n e
  | _, .bagUnion a b => .appendList (bagToList a) (bagToList b)
  | _, .bagDiff a b => .diffList (bagToList a) (bagToList b)

/-! `bagToList` matches only the constructors that can land at bag sort, so its matcher
discriminates on the index and does not reduce definitionally. These are its equations. -/

@[simp] theorem Expr.bagToList_var {c : Color} (x : String) :
    Expr.bagToList (.var x (.bag c)) = .var x (.list c) := by simp [Expr.bagToList]

@[simp] theorem Expr.bagToList_emptyBag {c : Color} :
    Expr.bagToList (.emptyBag c) = .nilList c := by simp [Expr.bagToList]

@[simp] theorem Expr.bagToList_single {c : Color} (n : Nat) (e : Expr (.color c)) :
    Expr.bagToList (.single n e) = Expr.replicateT n e := by simp [Expr.bagToList]

@[simp] theorem Expr.bagToList_bagUnion {c : Color} (a b : Expr (.bag c)) :
    Expr.bagToList (.bagUnion a b) = .appendList (Expr.bagToList a) (Expr.bagToList b) := by
  simp [Expr.bagToList]

@[simp] theorem Expr.bagToList_bagDiff {c : Color} (a b : Expr (.bag c)) :
    Expr.bagToList (.bagDiff a b) = .diffList (Expr.bagToList a) (Expr.bagToList b) := by
  simp [Expr.bagToList]

/-- **The list term represents the bag term.**

Under two environments that agree on the term's free variables -- which are all color-sorted,
so the list and bag environments agree on all of them -- the list the translation builds has,
for every token, exactly the coefficient the bag has. -/
theorem Expr.coeff_bagToList : ∀ {c : Color} (e : Expr (.bag c)) {lenv benv : Env},
    (∀ q ∈ e.freeVars, q.2.isColor = true) →
    (∀ q ∈ e.freeVars, lenv q.2 q.1 = benv q.2 q.1) →
    ∀ v : Value, countOf (Expr.eval (bagToList e) lenv) v = (Expr.eval e benv).coeff v
  | _, .var x (.bag c'), _, _, hcol, _, _ => by
      have := hcol (x, ExprTy.bag c') (List.mem_singleton.2 rfl)
      simp [ExprTy.isColor] at this
  | _, .emptyBag _, _, _, _, _, _ => by
      rw [Expr.bagToList_emptyBag]; rfl
  | _, .single n e, _, _, _, hag, v => by
      rw [Expr.bagToList_single]
      show countOf (Expr.eval (replicateT n e) _) v = (Bag.single n (Expr.eval e _)).coeff v
      rw [countOf_eval_replicateT, Bag.coeff_single, Expr.eval_congr e hag]
  | _, .bagUnion a b, _, _, hcol, hag, v => by
      rw [Expr.bagToList_bagUnion]
      show countOf (Expr.eval (bagToList a) _ ++ Expr.eval (bagToList b) _) v = _
      rw [countOf_append,
        coeff_bagToList a (fun q hq => hcol q (List.mem_append_left _ hq))
          (fun q hq => hag q (List.mem_append_left _ hq)) v,
        coeff_bagToList b (fun q hq => hcol q (List.mem_append_right _ hq))
          (fun q hq => hag q (List.mem_append_right _ hq)) v]
      exact (Bag.coeff_union _ _ v).symm
  | _, .bagDiff a b, _, _, hcol, hag, v => by
      rw [Expr.bagToList_bagDiff]
      show countOf (listDiff (Expr.eval (bagToList a) _) (Expr.eval (bagToList b) _)) v = _
      rw [countOf_listDiff,
        coeff_bagToList a (fun q hq => hcol q (List.mem_append_left _ hq))
          (fun q hq => hag q (List.mem_append_left _ hq)) v,
        coeff_bagToList b (fun q hq => hcol q (List.mem_append_right _ hq))
          (fun q hq => hag q (List.mem_append_right _ hq)) v]
      exact (Bag.coeff_diff _ _ v).symm


/-! ## The list-encoded LPE -/

/-- The state of the list-encoded process: a list of tokens per place. -/
def ListMarking := String → List Value

/-- The environment the list-encoded terms are read in: the place parameters hold the lists,
the summation variables hold the binding. The counterpart of `Marking.toEnv`. -/
def ListMarking.toEnv (LM : ListMarking) (b : Env) : Env
  | .color c, x => b (.color c) x
  | .bag _, _ => ∅
  | .list _, x => LM x

@[simp] theorem ListMarking.toEnv_color (LM : ListMarking) (b : Env) (c : Color) (x : String) :
    LM.toEnv b (.color c) x = b (.color c) x := rfl

@[simp] theorem ListMarking.toEnv_list (LM : ListMarking) (b : Env) (c : Color) (x : String) :
    LM.toEnv b (.list c) x = LM x := rfl

/-- Two markings represent the same bags.

This is the relation the refinement is stated over, and it is deliberately *not* an equality of
lists: `Implementation/docs/Plan.md` §5's order problem is exactly that two production orders
give distinct lists here, and nothing below ever asks them to be equal. -/
def listRel (LM : ListMarking) (M : Marking) : Prop :=
  ∀ p v, countOf (LM p) v = (M p).coeff v

/-- A term of the state, at list sort. -/
structure ListTerm where
  /-- The color the list holds. -/
  color : Color
  /-- The term. -/
  term : Expr (.list color)

/-- One summand of the list-encoded LPE. -/
structure ListSummand where
  /-- `H_k`, as the list of variables the `sum` binds. -/
  binder : Ctx
  /-- `c_k`, over the list parameters and the binder. -/
  cond : Expr (.color .bool)
  /-- `a_k ∈ Act`. -/
  act : String
  /-- `g_k`, as one list term per place. -/
  next : List (String × ListTerm)

/-- Definition 13 with a list per place instead of a bag. -/
structure ListLpe where
  /-- The colors whose sorts the specification declares. -/
  sorts : List Color
  /-- `D`, as one list parameter per place. -/
  params : List (String × Color)
  /-- `Act`. -/
  acts : List String
  /-- The summands. -/
  summands : List ListSummand
  /-- `d₀`. -/
  init : List (String × ListTerm)

/-- The marking a summand leads to. Unlike the bag encoding this is an equality and not an
equivalence: mCRL2's `List` is a free datatype, so the reached state is one particular list --
which is precisely why the order problem needs an argument. -/
def ListSummand.nextMarking (S : ListSummand) (LM : ListMarking) (b : Env) : ListMarking :=
  fun p =>
    match List.lookup p S.next with
    | some lt => Expr.eval lt.term (LM.toEnv b)
    | none => LM p

/-- `d₀`, evaluated. -/
def ListLpe.initMarking (L : ListLpe) : ListMarking := fun p =>
  match List.lookup p L.init with
  | some lt => Expr.eval lt.term Env.junk
  | none => []

/-- Definition 15 for the list encoding. -/
def ListLpe.step (L : ListLpe) (LM : ListMarking) (a : String) (LM' : ListMarking) : Prop :=
  ∃ S ∈ L.summands, S.act = a ∧ ∃ b : Env, b.WfOn S.binder ∧
    Expr.Holds S.cond (LM.toEnv b) ∧ ∀ p, LM' p = S.nextMarking LM b p

/-! ## The translation -/

namespace Net

/-- One conjunct of `c_t`, in the list encoding: `E(p,t)` is contained in the list at `p`. -/
def listCondConjunct (a : ArcDecl) : Expr (.color .bool) :=
  .subList (Expr.bagToList a.expr) (.var a.place (.list a.color))

/-- `c_t`, in the list encoding. -/
def listCondTerm (N : Net) (t : TransDecl) : Expr (.color .bool) :=
  Expr.andAll ((N.pre t.name).map listCondConjunct ++ [t.guard])

/-- The list at `p` after `t` has taken its tokens out. Where there is no arc the list is
unchanged rather than differenced against the empty list, which is what keeps the emitted text
free of the `\ ∅` the bag encoding writes. -/
def listConsumed (N : Net) (t : TransDecl) (d : PlaceDecl) : Expr (.list d.color) :=
  match N.inArc? d.name t.name with
  | some a => .diffList (.var d.name (.list d.color)) (Expr.bagToList (a.exprAt d.color))
  | none => .var d.name (.list d.color)

/-- `g_t` at the place `d`, in the list encoding. -/
def listNextTerm (N : Net) (t : TransDecl) (d : PlaceDecl) : Expr (.list d.color) :=
  match N.outArc? t.name d.name with
  | some a => .appendList (N.listConsumed t d) (Expr.bagToList (a.exprAt d.color))
  | none => N.listConsumed t d

/-- The summand of `t`, in the list encoding. -/
def listSummandOf (N : Net) (t : TransDecl) : ListSummand where
  binder := N.Var t
  cond := N.listCondTerm t
  act := t.name
  next := N.places.map fun d => (d.name, ⟨d.color, N.listNextTerm t d⟩)

/-- **The list-encoded LPE**: `Implementation/docs/Plan.md` §5's second backend, behind the
same translation as the first. -/
def toLpeList (N : Net) : ListLpe where
  sorts := N.colors
  params := N.places.map fun d => (d.name, d.color)
  acts := N.transNames
  summands := N.transitions.map N.listSummandOf
  init := N.places.map fun d => (d.name, ⟨d.color, Expr.bagToList d.init⟩)

/-! ## The refinement

Everything below compares the list encoding with the bag encoding of
`Cpn2mCrl2/Translate.lean`, which `Cpn2mCrl2/Correct.lean` has already tied to Definitions 6
and 7. Composing the two is what makes the list encoding as justified as the bag one. -/

variable {N : Net}

theorem isColor_of_scoped (h : N.Valid) {τ : ExprTy} {e : Expr τ}
    (hs : Expr.ScopedIn N.vars e) : ∀ q ∈ e.freeVars, q.2.isColor = true :=
  fun q hq => h.varsAreColors q (hs q hq)

theorem agree_toEnvList {Γ : Ctx} (hcol : ∀ q ∈ Γ, q.2.isColor = true) (LM : ListMarking)
    (b : Env) : ∀ q ∈ Γ, LM.toEnv b q.2 q.1 = b q.2 q.1 := by
  rintro ⟨x, τ⟩ hq
  have hc := hcol _ hq
  cases τ with
  | color c => rfl
  | bag c => simp [ExprTy.isColor] at hc
  | list c => simp [ExprTy.isColor] at hc

/-- An expression of the net is evaluated the same in the list environment and in the binding
alone -- obligation 4 of `Implementation/docs/Plan.md` §4 once more, now separating the list
parameters from the summation variables. -/
theorem eval_toEnvList (h : N.Valid) {τ : ExprTy} {e : Expr τ} (hs : Expr.ScopedIn N.vars e)
    (LM : ListMarking) (b : Env) : Expr.eval e (LM.toEnv b) = Expr.eval e b :=
  Expr.eval_congr e (agree_toEnvList (isColor_of_scoped h hs) LM b)

theorem inArc?_color (h : N.Valid) {t : String} {d : PlaceDecl} (hd : d ∈ N.places)
    {a : ArcDecl} (hf : N.inArc? d.name t = some a) : a.color = d.color := by
  have hpred := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  have h1 := h.inArcPlace a (List.mem_of_find?_eq_some hf)
  rw [hpred.1] at h1
  exact Option.some.inj (h1.symm.trans (placeColor?_of_mem h hd))

theorem outArc?_color (h : N.Valid) {t : String} {d : PlaceDecl} (hd : d ∈ N.places)
    {a : ArcDecl} (hf : N.outArc? t d.name = some a) : a.color = d.color := by
  have hpred := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  have h1 := h.outArcPlace a (List.mem_of_find?_eq_some hf)
  rw [hpred.1] at h1
  exact Option.some.inj (h1.symm.trans (placeColor?_of_mem h hd))

/-- The list an in-arc's expression translates to represents the bag it evaluates to. -/
theorem countOf_bagToList_in (h : N.Valid) {a : ArcDecl} (ha : a ∈ N.inArcs) {c : Color}
    (hc : a.color = c) (LM : ListMarking) (b : Env) (v : Value) :
    countOf (Expr.eval (Expr.bagToList (a.exprAt c)) (LM.toEnv b)) v
      = (Expr.eval a.expr b).coeff v := by
  have hs : Expr.ScopedIn N.vars (a.exprAt c) :=
    ArcDecl.scopedIn_exprAt (h.inArcScoped a ha) c
  rw [Expr.coeff_bagToList (a.exprAt c) (isColor_of_scoped h hs)
    (agree_toEnvList (isColor_of_scoped h hs) LM b) v, ArcDecl.eval_exprAt hc]

/-- The same for an out-arc. -/
theorem countOf_bagToList_out (h : N.Valid) {a : ArcDecl} (ha : a ∈ N.outArcs) {c : Color}
    (hc : a.color = c) (LM : ListMarking) (b : Env) (v : Value) :
    countOf (Expr.eval (Expr.bagToList (a.exprAt c)) (LM.toEnv b)) v
      = (Expr.eval a.expr b).coeff v := by
  have hs : Expr.ScopedIn N.vars (a.exprAt c) :=
    ArcDecl.scopedIn_exprAt (h.outArcScoped a ha) c
  rw [Expr.coeff_bagToList (a.exprAt c) (isColor_of_scoped h hs)
    (agree_toEnvList (isColor_of_scoped h hs) LM b) v, ArcDecl.eval_exprAt hc]

/-! ### `c_t` -/

theorem holds_listCondConjunct (h : N.Valid) {a : ArcDecl} (ha : a ∈ N.inArcs)
    {LM : ListMarking} {M : Marking} (hR : listRel LM M) (b : Env) :
    Expr.Holds (listCondConjunct a) (LM.toEnv b) ↔ Expr.eval a.expr b ⊆ M a.place := by
  show (subMultiset (Expr.eval (Expr.bagToList a.expr) (LM.toEnv b)) (LM a.place) = true) ↔ _
  rw [subMultiset_iff]
  have hkey : ∀ v, countOf (Expr.eval (Expr.bagToList a.expr) (LM.toEnv b)) v
      = (Expr.eval a.expr b).coeff v := by
    intro v
    have hb := countOf_bagToList_in h ha (c := a.color) rfl LM b v
    rwa [ArcDecl.exprAt_self] at hb
  simp only [hkey, hR a.place]
  exact Iff.rfl

/-- **The condition of the list encoding is the condition of the bag encoding.** -/
theorem holds_listCondTerm (h : N.Valid) {t : TransDecl} (ht : t ∈ N.transitions)
    {LM : ListMarking} {M : Marking} (hR : listRel LM M) (b : Env) :
    Expr.Holds (N.listCondTerm t) (LM.toEnv b) ↔ N.Enabled M t b := by
  rw [listCondTerm, Expr.holds_andAll]
  have hguard : Expr.Holds t.guard (LM.toEnv b) ↔ Expr.Holds t.guard b := by
    unfold Expr.Holds
    rw [eval_toEnvList h (h.guardScoped t ht) LM b]
  constructor
  · intro hall
    refine ⟨fun a ha => ?_, hguard.1
      (hall _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))⟩
    exact (holds_listCondConjunct h (mem_inArcs_of_mem_pre ha) hR b).1
      (hall _ (List.mem_append_left _ (List.mem_map_of_mem ha)))
  · rintro ⟨hpre, hg⟩ e he
    rcases List.mem_append.1 he with he' | he'
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he'
      exact (holds_listCondConjunct h (mem_inArcs_of_mem_pre ha) hR b).2 (hpre a ha)
    · rw [List.mem_singleton.1 he']
      exact hguard.2 hg

/-! ### `g_t` -/

theorem countOf_listConsumed (h : N.Valid) (t : TransDecl) {d : PlaceDecl}
    (hd : d ∈ N.places) {LM : ListMarking} {M : Marking} (hR : listRel LM M) (b : Env)
    (v : Value) :
    countOf (Expr.eval (N.listConsumed t d) (LM.toEnv b)) v
      = (M d.name).coeff v - (N.consume t.name b d.name).coeff v := by
  unfold listConsumed Net.consume
  cases hf : N.inArc? d.name t.name with
  | none =>
    show countOf (LM d.name) v = _
    simpa using hR d.name v
  | some a =>
    show countOf (listDiff (LM d.name) _) v = _
    rw [countOf_listDiff, hR d.name v,
      countOf_bagToList_in h (List.mem_of_find?_eq_some hf) (inArc?_color h hd hf) LM b v]

theorem countOf_listNextTerm (h : N.Valid) (t : TransDecl) {d : PlaceDecl}
    (hd : d ∈ N.places) {LM : ListMarking} {M : Marking} (hR : listRel LM M) (b : Env)
    (v : Value) :
    countOf (Expr.eval (N.listNextTerm t d) (LM.toEnv b)) v
      = (N.fire M t b d.name).coeff v := by
  show _ = ((M d.name \ N.consume t.name b d.name) ∪ N.produce t.name b d.name).coeff v
  rw [Bag.coeff_union, Bag.coeff_diff]
  unfold listNextTerm Net.produce
  cases hf : N.outArc? t.name d.name with
  | none => simpa using countOf_listConsumed h t hd hR b v
  | some a =>
    show countOf (Expr.eval (N.listConsumed t d) _ ++ _) v = _
    rw [countOf_append, countOf_listConsumed h t hd hR b v,
      countOf_bagToList_out h (List.mem_of_find?_eq_some hf) (outArc?_color h hd hf) LM b v]

/-- **The next state of the list encoding represents the next state of the bag encoding.** -/
theorem countOf_listNextMarking (h : N.Valid) (t : TransDecl) {LM : ListMarking}
    {M : Marking} (hR : listRel LM M) (b : Env) (p : String) (v : Value) :
    countOf ((N.listSummandOf t).nextMarking LM b p) v = (N.fire M t b p).coeff v := by
  by_cases hp : p ∈ N.placeNames
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
    have hlk : List.lookup d.name (N.listSummandOf t).next
        = some ⟨d.color, N.listNextTerm t d⟩ :=
      lookup_name_of_mem (fun e => (⟨e.color, N.listNextTerm t e⟩ : ListTerm)) h.placesNodup hd
    have heq : (N.listSummandOf t).nextMarking LM b d.name
        = Expr.eval (N.listNextTerm t d) (LM.toEnv b) := by
      simp only [ListSummand.nextMarking, hlk]
    rw [heq, countOf_listNextTerm h t hd hR b v]
  · have hin : N.inArc? p t.name = none := by
      cases hf : N.inArc? p t.name with
      | none => rfl
      | some a =>
        have hplace : a.place = p := by
          have hpred := List.find?_some hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hpred
          exact hpred.1
        exact absurd (hplace ▸ mem_placeNames_of_placeColor?
          (h.inArcPlace a (List.mem_of_find?_eq_some hf))) hp
    have hout : N.outArc? t.name p = none := by
      cases hf : N.outArc? t.name p with
      | none => rfl
      | some a =>
        have hplace : a.place = p := by
          have hpred := List.find?_some hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hpred
          exact hpred.1
        exact absurd (hplace ▸ mem_placeNames_of_placeColor?
          (h.outArcPlace a (List.mem_of_find?_eq_some hf))) hp
    have hlk : List.lookup p (N.listSummandOf t).next = none :=
      lookup_name_of_not_mem (fun e => (⟨e.color, N.listNextTerm t e⟩ : ListTerm)) hp
    have heq : (N.listSummandOf t).nextMarking LM b p = LM p := by
      simp only [ListSummand.nextMarking, hlk]
    rw [heq, hR p v]
    show _ = ((M p \ N.consume t.name b p) ∪ N.produce t.name b p).coeff v
    simp [Net.consume, Net.produce, hin, hout]

/-! ### The two halves of the refinement -/

/-- A step of the list encoding is a step of the bag encoding. -/
theorem step_of_toLpeList_step (h : N.Valid) {LM : ListMarking} {M : Marking}
    (hR : listRel LM M) {a : String} {LM' : ListMarking}
    (hstep : N.toLpeList.step LM a LM') :
    ∃ M' : Marking, N.toLpe.step M a M' ∧ listRel LM' M' := by
  obtain ⟨S, hS, hact, b, hb, hcond, hnext⟩ := hstep
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hS
  refine ⟨N.fire M t b, ?_, fun p v => ?_⟩
  · exact (N.toLpe_step h M a _).2 ⟨t, ht, hact, b, hb,
      (holds_listCondTerm h ht hR b).1 hcond, fun _ => Bag.Equiv.rfl _⟩
  · rw [hnext p]
    exact countOf_listNextMarking h t hR b p v

/-- A step of the bag encoding is a step of the list encoding.

Together with `step_of_toLpeList_step` this is the refinement `Implementation/docs/Plan.md` §5
says nobody has proved. The list state it produces is one particular representative; any other
representative of the same bags would have done, which is the order problem answered. -/
theorem toLpeList_step_of_step (h : N.Valid) {LM : ListMarking} {M : Marking}
    (hR : listRel LM M) {a : String} {M' : Marking} (hstep : N.toLpe.step M a M') :
    ∃ LM' : ListMarking, N.toLpeList.step LM a LM' ∧ listRel LM' M' := by
  obtain ⟨t, ht, hname, b, hb, hen, hfire⟩ := (N.toLpe_step h M a M').1 hstep
  refine ⟨(N.listSummandOf t).nextMarking LM b, ⟨N.listSummandOf t,
    List.mem_map_of_mem ht, hname, b, hb, (holds_listCondTerm h ht hR b).2 hen,
    fun _ => rfl⟩, fun p v => ?_⟩
  rw [countOf_listNextMarking h t hR b p v, ← hfire p v]

/-- The two encodings start in markings that represent the same bags. -/
theorem listRel_init (h : N.Valid) : listRel N.toLpeList.initMarking N.toLpe.initMarking := by
  intro p v
  by_cases hp : p ∈ N.placeNames
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
    have hlk : List.lookup d.name N.toLpeList.init
        = some ⟨d.color, Expr.bagToList d.init⟩ :=
      lookup_name_of_mem (fun e => (⟨e.color, Expr.bagToList e.init⟩ : ListTerm))
        h.placesNodup hd
    have hlk' : List.lookup d.name N.toLpe.init = some ⟨d.color, d.init⟩ :=
      lookup_name_of_mem (fun e => (⟨e.color, e.init⟩ : BagTerm)) h.placesNodup hd
    show countOf (match List.lookup d.name N.toLpeList.init with
      | some lt => Expr.eval lt.term Env.junk
      | none => []) v = _
    rw [hlk]
    show _ = (match List.lookup d.name N.toLpe.init with
      | some bt => Expr.eval bt.term Env.junk
      | none => ∅).coeff v
    rw [hlk']
    refine Expr.coeff_bagToList d.init ?_ (fun _ _ => rfl) v
    intro q hq
    rw [h.initClosed d hd] at hq
    cases hq
  · have hlk : List.lookup p N.toLpeList.init = none :=
      lookup_name_of_not_mem (fun e => (⟨e.color, Expr.bagToList e.init⟩ : ListTerm)) hp
    have hlk' : List.lookup p N.toLpe.init = none :=
      lookup_name_of_not_mem (fun e => (⟨e.color, e.init⟩ : BagTerm)) hp
    show countOf (match List.lookup p N.toLpeList.init with
      | some lt => Expr.eval lt.term Env.junk
      | none => []) v = _
    rw [hlk]
    show _ = (match List.lookup p N.toLpe.init with
      | some bt => Expr.eval bt.term Env.junk
      | none => ∅).coeff v
    rw [hlk']
    rfl

end Net

end Cpn2mCrl2
