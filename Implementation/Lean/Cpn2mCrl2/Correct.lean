/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Translate

/-!
# Correctness of the translation

Tier T2 of `Implementation/docs/Plan.md` §2:

> The emitted LPE term *denotes* the `c_t` and `g_t` of Definition 14.

`Proof/MCRL2.lean` has the same two statements, `toLPE_cond` and `toLPE_next`, and both hold
there by `rfl`, because both sides are transcriptions of one formula.
`Thesis/docs/LeanFormalization.md` §5.1 says what has to change for them to stop being
bookkeeping:

> `LPE.cond` and `LPE.next` become terms and `LPE.semantics` denotes them, so `toLPE_cond` and `toLPE_next` stop holding by `rfl` and become theorems proved from the evaluation equations.

That is what `Net.toLpe_cond` and `Net.toLpe_next` are here. Neither is `rfl`. Each is proved
from the evaluation equations of `Cpn2mCrl2/Expr.lean`, from the coefficient laws of
`Cpn2mCrl2/Bag.lean` -- `Bag.subsetB_iff` is what makes the emitted `⊆` a `Bool`-valued term
at all, which is `Implementation/docs/Plan.md` §4.1 -- and from `Expr.eval_congr`, obligation
4, which is where the place parameters and the summation variables are separated.

`Net.toLpe_step` composes the two: one step of the LTS the emitted specification denotes is
one step of the CPN's reachability graph, and conversely.

## What this does and does not establish

It establishes T2. Composed with Theorem 1 -- `CPN.bisimulation_transRel` of
`Proof/Soundness.lean`, tier T3, already proved -- it is the statement
`Implementation/docs/Plan.md` §2 calls "the theorem the project is for". That composition is
*not* carried out mechanically here: `Proof/` is stated over an abstract `ExprLang` and needs
Mathlib, and this package deliberately does not. See `Implementation/Lean/README.md` for what
the bridge would involve.

It does not establish T0 or T4 -- that `mcrl22lps` accepts the printed text, and that what the
tool reads back denotes the term that was printed. `Implementation/docs/Plan.md` §2 calls
those "the honest ceiling", and `scripts/check.sh` tests them.

## Main results

* `Net.toLpe_cond` : the emitted condition denotes Definition 6's enabledness.
* `Net.toLpe_next` : the emitted next-state term denotes Definition 7's marking.
* `Net.toLpe_step` : the two transition relations agree.
-/

namespace Cpn2mCrl2

namespace Net

variable {N : Net}

/-! ### Looking a place up by name

Definition 5 makes `C` and `I` functions on `P`. Here `P` is a list, so reading `C(p)` off it
is a `find?`, and that it finds the right declaration is where `Net.Valid.placesNodup` -- one
of the side conditions `Thesis/docs/LeanFormalization.md` §4.5 records as inert in `Proof/` --
starts doing work. -/

theorem find?_name_of_mem : ∀ {l : List PlaceDecl}, ListUtil.NoDup (l.map PlaceDecl.name) →
    ∀ {d : PlaceDecl}, d ∈ l → l.find? (fun e => e.name == d.name) = some d := by
  intro l
  induction l with
  | nil => intro _ d hd; cases hd
  | cons e tl ih =>
    intro hnd d hd
    by_cases he : e.name = d.name
    · have hed : e = d := by
        rcases List.mem_cons.1 hd with h | h
        · exact h.symm
        · exact absurd (he ▸ List.mem_map_of_mem (f := PlaceDecl.name) h) hnd.1
      exact List.find?_cons_of_pos (by simp [he]) |>.trans (by rw [hed])
    · have hdt : d ∈ tl := by
        rcases List.mem_cons.1 hd with h | h
        · exact absurd (congrArg PlaceDecl.name h.symm) he
        · exact h
      rw [List.find?_cons_of_neg (by simp [he])]
      exact ih hnd.2 hdt

theorem lookup_name_of_mem {β : Type} (f : PlaceDecl → β) :
    ∀ {l : List PlaceDecl}, ListUtil.NoDup (l.map PlaceDecl.name) →
      ∀ {d : PlaceDecl}, d ∈ l →
        List.lookup d.name (l.map fun e => (e.name, f e)) = some (f d) := by
  intro l
  induction l with
  | nil => intro _ d hd; cases hd
  | cons e tl ih =>
    intro hnd d hd
    by_cases he : e.name = d.name
    · have hed : e = d := by
        rcases List.mem_cons.1 hd with h | h
        · exact h.symm
        · exact absurd (he ▸ List.mem_map_of_mem (f := PlaceDecl.name) h) hnd.1
      have hbeq : (d.name == e.name) = true := by simp [he]
      rw [List.map_cons, List.lookup_cons, hbeq, hed]
    · have hdt : d ∈ tl := by
        rcases List.mem_cons.1 hd with h | h
        · exact absurd (congrArg PlaceDecl.name h.symm) he
        · exact h
      have hne : d.name ≠ e.name := fun hq => he hq.symm
      have hbeq : (d.name == e.name) = false := by simp [hne]
      rw [List.map_cons, List.lookup_cons, hbeq]
      exact ih hnd.2 hdt

theorem lookup_name_of_not_mem {β : Type} (f : PlaceDecl → β) :
    ∀ {l : List PlaceDecl} {p : String}, p ∉ l.map PlaceDecl.name →
      List.lookup p (l.map fun e => (e.name, f e)) = none := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons e tl ih =>
    intro p hp
    have hne : ¬ (p = e.name) := fun h => hp (h ▸ List.mem_cons_self ..)
    have htl : p ∉ tl.map PlaceDecl.name := fun h => hp (List.mem_cons_of_mem _ h)
    have hbeq : (p == e.name) = false := by simp [hne]
    rw [List.map_cons, List.lookup_cons, hbeq]
    exact ih htl

theorem placeColor?_of_mem (h : N.Valid) {d : PlaceDecl} (hd : d ∈ N.places) :
    N.placeColor? d.name = some d.color := by
  unfold placeColor?
  rw [find?_name_of_mem h.placesNodup hd]
  rfl

theorem mem_placeNames_of_placeColor? {x : String} {c : Color}
    (hx : N.placeColor? x = some c) : x ∈ N.placeNames := by
  unfold placeColor? at hx
  cases hf : N.places.find? (fun d => d.name == x) with
  | none => rw [hf] at hx; exact absurd hx (by simp)
  | some d =>
    have hmem : d ∈ N.places := List.mem_of_find?_eq_some hf
    have hname : d.name = x := by
      have := List.find?_some hf
      simpa using this
    exact hname ▸ List.mem_map_of_mem (f := PlaceDecl.name) hmem

/-! ### The two environments agree where an expression can see

The place parameters and the summation variables are separate halves of `Marking.toEnv`, and
a CPN's own expressions only ever mention the second half -- `Net.Valid.varsAreColors`. This
is obligation 4 of `Implementation/docs/Plan.md` §4 in the form the translation needs it. -/

theorem eval_toEnv (h : N.Valid) {τ : ExprTy} {e : Expr τ} (hs : Expr.ScopedIn N.vars e)
    (M : Marking) (b : Env) : Expr.eval e (M.toEnv b) = Expr.eval e b := by
  refine Expr.eval_congr_of_scoped hs ?_
  rintro ⟨x, τ'⟩ hq
  have hc := h.varsAreColors _ hq
  cases τ' with
  | color c => rfl
  | bag c => simp [ExprTy.isColor] at hc

theorem holds_toEnv (h : N.Valid) {e : Expr (.color .bool)} (hs : Expr.ScopedIn N.vars e)
    (M : Marking) (b : Env) : Expr.Holds e (M.toEnv b) ↔ Expr.Holds e b := by
  unfold Expr.Holds
  rw [eval_toEnv h hs]

/-! ### `c_t` -/

/-- One conjunct of the emitted condition denotes one conjunct of Definition 6.

`Bag.subsetB_iff` is the step that needs finite support: the emitted `⊆` is a `Bool`-valued
term, and `Implementation/docs/Plan.md` §4.1 records that this is only possible because bags
here are finitely supported. -/
theorem holds_condConjunct (h : N.Valid) {a : ArcDecl} (ha : a ∈ N.inArcs) (M : Marking)
    (b : Env) : Expr.Holds a.condConjunct (M.toEnv b) ↔ Expr.eval a.expr b ⊆ M a.place := by
  show (Value.asBool (Expr.eval (Expr.bagSubset a.expr (.var a.place (.bag a.color)))
    (M.toEnv b))) = true ↔ _
  rw [show Expr.eval (Expr.bagSubset a.expr (.var a.place (.bag a.color))) (M.toEnv b)
      = Value.bool (Bag.subsetB (Expr.eval a.expr (M.toEnv b))
          (Expr.eval (Expr.var a.place (ExprTy.bag a.color)) (M.toEnv b))) from rfl]
  rw [show Expr.eval (Expr.var a.place (ExprTy.bag a.color)) (M.toEnv b) = M a.place from rfl]
  rw [eval_toEnv h (h.inArcScoped a ha)]
  exact Bag.subsetB_iff _ _

/-- **`c_t` denotes Definition 6.**

`Proof/MCRL2.lean`'s `toLPE_cond` is `rfl`; this one is not. It is proved from the evaluation
equations of `Expr`, from `Bag.subsetB_iff`, and from obligation 4 in the form `eval_toEnv`. -/
theorem toLpe_cond (h : N.Valid) (t : TransDecl) (ht : t ∈ N.transitions) (M : Marking)
    (b : Env) : Expr.Holds (N.condTerm t) (M.toEnv b) ↔ N.Enabled M t b := by
  rw [condTerm, Expr.holds_andAll]
  constructor
  · intro hall
    refine ⟨fun a ha => ?_, ?_⟩
    · have hmem : a ∈ N.inArcs := mem_inArcs_of_mem_pre ha
      exact (holds_condConjunct h hmem M b).1
        (hall _ (List.mem_append_left _ (List.mem_map_of_mem ha)))
    · exact (holds_toEnv h (h.guardScoped t ht) M b).1
        (hall _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))
  · rintro ⟨hpre, hguard⟩ e he
    rcases List.mem_append.1 he with he' | he'
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he'
      exact (holds_condConjunct h (mem_inArcs_of_mem_pre ha) M b).2 (hpre a ha)
    · rw [List.mem_singleton.1 he']
      exact (holds_toEnv h (h.guardScoped t ht) M b).2 hguard

/-! ### `g_t` -/

theorem eval_consumeTerm (h : N.Valid) (t : TransDecl) {d : PlaceDecl} (hd : d ∈ N.places)
    (M : Marking) (b : Env) :
    Expr.eval (N.consumeTerm t d) (M.toEnv b) = N.consume t.name b d.name := by
  unfold consumeTerm consume
  cases hf : N.inArc? d.name t.name with
  | none => rfl
  | some a =>
    have hmem : a ∈ N.inArcs := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    have hplace : a.place = d.name := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      exact hpred.1
    have hcolor : a.color = d.color := by
      have h1 := h.inArcPlace a hmem
      rw [hplace] at h1
      exact Option.some.inj (h1.symm.trans (placeColor?_of_mem h hd))
    rw [ArcDecl.eval_exprAt hcolor]
    exact eval_toEnv h (h.inArcScoped a hmem) M b

theorem eval_produceTerm (h : N.Valid) (t : TransDecl) {d : PlaceDecl} (hd : d ∈ N.places)
    (M : Marking) (b : Env) :
    Expr.eval (N.produceTerm t d) (M.toEnv b) = N.produce t.name b d.name := by
  unfold produceTerm produce
  cases hf : N.outArc? t.name d.name with
  | none => rfl
  | some a =>
    have hmem : a ∈ N.outArcs := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    have hplace : a.place = d.name := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      exact hpred.1
    have hcolor : a.color = d.color := by
      have h1 := h.outArcPlace a hmem
      rw [hplace] at h1
      exact Option.some.inj (h1.symm.trans (placeColor?_of_mem h hd))
    rw [ArcDecl.eval_exprAt hcolor]
    exact eval_toEnv h (h.outArcScoped a hmem) M b

/-- **`g_t` denotes Definition 7.**

The component of the emitted next state for a place evaluates to the bag Definition 7 puts in
that place. Like `toLpe_cond`, and unlike `Proof/MCRL2.lean`'s `toLPE_next`, this is not
`rfl`. -/
theorem toLpe_next (h : N.Valid) (t : TransDecl) {d : PlaceDecl} (hd : d ∈ N.places)
    (M : Marking) (b : Env) :
    Expr.eval (N.nextTerm t d) (M.toEnv b) = N.fire M t b d.name := by
  show Expr.eval (Expr.bagUnion (Expr.bagDiff (Expr.var d.name (ExprTy.bag d.color))
    (N.consumeTerm t d)) (N.produceTerm t d)) (M.toEnv b) = _
  rw [show Expr.eval (Expr.bagUnion (Expr.bagDiff (Expr.var d.name (ExprTy.bag d.color))
        (N.consumeTerm t d)) (N.produceTerm t d)) (M.toEnv b)
      = (M d.name \ Expr.eval (N.consumeTerm t d) (M.toEnv b))
          ∪ Expr.eval (N.produceTerm t d) (M.toEnv b) from rfl]
  rw [eval_consumeTerm h t hd, eval_produceTerm h t hd]
  rfl

/-! ### The two transition relations -/

/-- A place the summand does not mention keeps its marking, and Definition 7 agrees, because
every arc of a valid net names a place. -/
theorem nextMarking_equiv_fire (h : N.Valid) (t : TransDecl) (M : Marking) (b : Env)
    (p : String) : Bag.Equiv ((N.summandOf t).nextMarking M b p) (N.fire M t b p) := by
  by_cases hp : p ∈ N.placeNames
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
    have hlk : List.lookup d.name (N.summandOf t).next
        = some ⟨d.color, N.nextTerm t d⟩ :=
      lookup_name_of_mem (fun e => (⟨e.color, N.nextTerm t e⟩ : BagTerm)) h.placesNodup hd
    have heq : (N.summandOf t).nextMarking M b d.name
        = Expr.eval (N.nextTerm t d) (M.toEnv b) := by
      simp only [Summand.nextMarking, hlk]
    rw [heq, toLpe_next h t hd]
    exact Bag.Equiv.rfl _
  · have hin : N.inArc? p t.name = none := by
      cases hf : N.inArc? p t.name with
      | none => rfl
      | some a =>
        have hmem : a ∈ N.inArcs := List.mem_of_find?_eq_some hf
        have hplace : a.place = p := by
          have hpred := List.find?_some hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hpred
          exact hpred.1
        exact absurd (hplace ▸ mem_placeNames_of_placeColor? (h.inArcPlace a hmem)) hp
    have hout : N.outArc? t.name p = none := by
      cases hf : N.outArc? t.name p with
      | none => rfl
      | some a =>
        have hmem : a ∈ N.outArcs := List.mem_of_find?_eq_some hf
        have hplace : a.place = p := by
          have hpred := List.find?_some hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hpred
          exact hpred.1
        exact absurd (hplace ▸ mem_placeNames_of_placeColor? (h.outArcPlace a hmem)) hp
    have hlk : List.lookup p (N.summandOf t).next = none :=
      lookup_name_of_not_mem (fun e => (⟨e.color, N.nextTerm t e⟩ : BagTerm)) hp
    have heq : (N.summandOf t).nextMarking M b p = M p := by
      simp only [Summand.nextMarking, hlk]
    rw [heq]
    intro v
    show (M p).coeff v = ((M p \ N.consume t.name b p) ∪ N.produce t.name b p).coeff v
    simp [consume, produce, hin, hout]

/-- **T2, composed.**
One transition of the LTS the emitted specification denotes is one transition of the CPN's
reachability graph, and conversely.

This is the statement `Implementation/docs/Plan.md` §2 puts one composition away from the
theorem the project is for: with Theorem 1 of `Proof/Soundness.lean` on the other side, the
specification this program prints denotes an LTS bisimilar to the CPN's reachability graph. -/
theorem toLpe_step (h : N.Valid) (M : Marking) (a : String) (M' : Marking) :
    N.toLpe.step M a M' ↔ N.step M a M' := by
  constructor
  · rintro ⟨S, hS, hact, b, hcond, hnext⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hS
    refine ⟨t, ht, hact, b, ?_, fun p => ?_⟩
    · exact (toLpe_cond h t ht M b).1 hcond
    · exact Bag.Equiv.trans (hnext p) (nextMarking_equiv_fire h t M b p)
  · rintro ⟨t, ht, hname, b, hen, hnext⟩
    refine ⟨N.summandOf t, List.mem_map_of_mem ht, hname, b, ?_, fun p => ?_⟩
    · exact (toLpe_cond h t ht M b).2 hen
    · exact Bag.Equiv.trans (hnext p) (Bag.Equiv.symm (nextMarking_equiv_fire h t M b p))

end Net

end Cpn2mCrl2
