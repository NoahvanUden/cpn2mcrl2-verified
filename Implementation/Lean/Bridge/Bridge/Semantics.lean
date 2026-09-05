/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Bridge.Vars

/-!
# Definitions 6 and 7 on both sides

`Cpn2mCrl2/Semantics.lean` and `Proof/ColoredPetriNets.lean` both transcribe Definitions 6 and
7. This file shows they say the same thing about a validated `Net` and the `CPN` it denotes.

Three things have to be reconciled, and each is where a design decision of one side meets a
design decision of the other.

**Bindings.** `Proof/` gives a binding of `Var(t)` as a dependent function into the values of
each variable's color; `Cpn2mCrl2/Expr.lean` gives one as a total, untyped `Env` with a
separate `Env.WfOn`. `Net.envOfTransBinding` and `Net.transBindingOfEnv` convert, and
`Expr.eval_congr` -- obligation 4 of `Implementation/docs/Plan.md` §4 -- is what makes the
round trip invisible to any expression that is scoped where it should be.

**Bags.** `Proof/`'s bag over a place holds only values *of that place's color*; ours holds any
`Value`. `Bag.coeff_eq_zero_of_not_ofColor` closes the gap: a bag that `Cpn2mCrl2/Typing.lean`
says is well-typed has coefficient zero everywhere else, so the two agree.

**Quantifiers.** Definition 6 ranges over the places of `pre(t)`; ours ranges over the arcs
into `t`. `Bridge/Vars.lean` matches them up.

## Main results

* `Net.cpnEnabled_iff` : Definition 6 on both sides.
* `Net.cpnFire_coeff` : Definition 7 on both sides.
-/

namespace Cpn2mCrl2

namespace Net

/-! ## Bindings -/

/-- A binding of `Proof/`, read as one of ours. -/
noncomputable def envOfTransBinding {N : Net} (h : N.Valid) (t : N.TIdx)
    (b : (N.toCPN h).TransBinding t) : Env :=
  Bridge.envOfBinding N ((N.toCPN h).Var t) b

/-- `Var(t)` only ever mentions variables of `V`, which is what makes the conversions
well-typed. -/
theorem Var_subset_vars {N : Net} (h : N.Valid) {t : TransDecl} (ht : t ∈ N.transitions)
    {q : String × ExprTy} (hq : q ∈ N.Var t) : q ∈ N.vars := by
  have hq' := ListUtil.mem_dedup.1 hq
  rcases List.mem_append.1 hq' with hq' | hq'
  · rcases List.mem_append.1 hq' with hg | hpre
    · exact h.guardScoped t ht _ hg
    · obtain ⟨a, ha, hfa⟩ := List.mem_flatMap.1 hpre
      exact h.inArcScoped a (mem_inArcs_of_mem_pre ha) _ hfa
  · obtain ⟨a, ha, hfa⟩ := List.mem_flatMap.1 hq'
    exact h.outArcScoped a (mem_outArcs_of_mem_post ha) _ hfa

theorem wfOn_envOfTransBinding {N : Net} (h : N.Valid) (t : N.TIdx)
    (b : (N.toCPN h).TransBinding t) :
    (envOfTransBinding h t b).WfOn (N.Var (N.transAt t)) :=
  Bridge.wfOn_envOfBinding h b
    (fun _ hq => Var_subset_vars h (N.transAt_mem t) hq)
    (fun _ hq => mem_cpnVar_of_mem_Var h t hq)

/-- One of ours, read as a binding of `Proof/`. -/
def transBindingOfEnv {N : Net} (h : N.Valid) (t : N.TIdx) (b : Env)
    (hb : b.WfOn (N.Var (N.transAt t))) : (N.toCPN h).TransBinding t :=
  fun v => ⟨b (.color (N.varTypeOf v.1)) v.1, hb _ (mem_Var_of_mem_cpnVar h t v.2)⟩

/-! ## Evaluation

Everything below reduces to one fact: the environment `Proof/`'s `evalOn` builds and the
environment `envOfTransBinding` builds agree wherever the expression can look. -/

theorem eval_evalOn {N : Net} (h : N.Valid) (t : N.TIdx) (b : (N.toCPN h).TransBinding t)
    {ρ : _root_.ExprTy Color} (e : N.LangExpr ρ)
    (hsub : N.langVars e ⊆ (N.toCPN h).Var t) :
    Expr.eval e.1 (N.langEnv e (fun v => b ⟨v.1, hsub v.2⟩))
      = Expr.eval e.1 (envOfTransBinding h t b) := by
  refine Expr.eval_congr _ ?_
  rintro ⟨x, σ⟩ hx
  have hx1 : x ∈ N.langVars e := ⟨σ, hx⟩
  cases σ with
  | color c =>
    show Bridge.envOfBinding N (N.langVars e) (fun v => b ⟨v.1, hsub v.2⟩) (.color c) x
        = Bridge.envOfBinding N ((N.toCPN h).Var t) b (.color c) x
    rw [Bridge.envOfBinding_color (fun v => b ⟨v.1, hsub v.2⟩) hx1 c,
      Bridge.envOfBinding_color b (hsub hx1) c]
  | bag c => rfl
  | list c => rfl

theorem consumedBy_coeff {N : Net} (h : N.Valid) (t : N.TIdx)
    (b : (N.toCPN h).TransBinding t) (p : N.PIdx) (hp : (p, t) ∈ N.cpnInArc)
    (v : Bridge.Val (N.placeAt p).color) :
    CPN.consumedBy b p hp v =
      (Expr.eval (N.arcOfIn (p, t) hp).expr (envOfTransBinding h t b)).coeff v.1 := by
  rw [show CPN.consumedBy b p hp v
      = (Expr.eval ((N.toCPN h).Ein (p, t) hp).1.1
          (N.langEnv ((N.toCPN h).Ein (p, t) hp).1
            (fun w => b ⟨w.1, (N.toCPN h).vars_Ein_subset hp w.2⟩))).coeff v.1 from rfl]
  rw [eval_evalOn h t b _ ((N.toCPN h).vars_Ein_subset hp)]
  exact congrArg (fun m : Bag => m.coeff v.1)
    (ArcDecl.eval_exprAt (N.arcOfIn_color h (p, t) hp) (envOfTransBinding h t b))

theorem producedBy_coeff {N : Net} (h : N.Valid) (t : N.TIdx)
    (b : (N.toCPN h).TransBinding t) (p : N.PIdx) (hp : (t, p) ∈ N.cpnOutArc)
    (v : Bridge.Val (N.placeAt p).color) :
    CPN.producedBy b p hp v =
      (Expr.eval (N.arcOfOut (t, p) hp).expr (envOfTransBinding h t b)).coeff v.1 := by
  rw [show CPN.producedBy b p hp v
      = (Expr.eval ((N.toCPN h).Eout (t, p) hp).1.1
          (N.langEnv ((N.toCPN h).Eout (t, p) hp).1
            (fun w => b ⟨w.1, (N.toCPN h).vars_Eout_subset hp w.2⟩))).coeff v.1 from rfl]
  rw [eval_evalOn h t b _ ((N.toCPN h).vars_Eout_subset hp)]
  exact congrArg (fun m : Bag => m.coeff v.1)
    (ArcDecl.eval_exprAt (N.arcOfOut_color h (t, p) hp) (envOfTransBinding h t b))

theorem holds_cpnG {N : Net} (h : N.Valid) (t : N.TIdx) (b : (N.toCPN h).TransBinding t) :
    ExprLang.Holds ((N.toCPN h).G t).1 ((N.toCPN h).vars_G_subset t) b ↔
      Expr.Holds (N.transAt t).guard (envOfTransBinding h t b) := by
  rw [show ExprLang.Holds ((N.toCPN h).G t).1 ((N.toCPN h).vars_G_subset t) b
      = ((Expr.eval ((N.toCPN h).G t).1.1
          (N.langEnv ((N.toCPN h).G t).1
            (fun w => b ⟨w.1, (N.toCPN h).vars_G_subset t w.2⟩))).asBool = true) from rfl]
  rw [eval_evalOn h t b _ ((N.toCPN h).vars_G_subset t)]
  exact Iff.rfl

/-! ## The marking relation -/

/-- A marking of `Proof/` and one of ours agree when they give every well-typed token the same
coefficient in every place.

Ours can carry tokens of the wrong color and `Proof/`'s cannot, which is why this is a
relation and not an isomorphism. It costs nothing: `Cpn2mCrl2/Typing.lean` says an arc
expression never produces one. -/
def markingRel {N : Net} (h : N.Valid) (d : (N.toCPN h).Marking) (M : Marking) : Prop :=
  ∀ (p : N.PIdx) (v : Bridge.Val (N.placeAt p).color),
    d p v = (M (N.placeAt p).name).coeff v.1

/-! ## Definition 6 -/

/-- An arc expression evaluates to a bag of the place's own color, so it has coefficient zero
at every token of any other. This is what lets a bag over all of `Value` be compared with a bag
over the values of one color. -/
theorem coeff_eval_eq_zero {a : ArcDecl} {b : Env} {Γ : Ctx} (hb : b.WfOn Γ)
    (hsub : ∀ q ∈ a.expr.freeVars, q ∈ Γ) {v : Value} (hv : v.ofColor a.color ≠ true) :
    (Expr.eval a.expr b).coeff v = 0 :=
  Bag.coeff_eq_zero_of_not_ofColor (Expr.eval_wf a.expr (fun q hq => hb q (hsub q hq))) hv

/-- **Definition 6, on both sides.** -/
theorem cpnEnabled_iff {N : Net} (h : N.Valid) (t : N.TIdx) (d : (N.toCPN h).Marking)
    (M : Marking) (hR : markingRel h d M) (b : (N.toCPN h).TransBinding t) :
    CPN.Enabled d b ↔ N.Enabled M (N.transAt t) (envOfTransBinding h t b) := by
  set b' := envOfTransBinding h t b with hb'def
  have hwf : b'.WfOn (N.Var (N.transAt t)) := wfOn_envOfTransBinding h t b
  constructor
  · rintro ⟨hpre, hguard⟩
    refine ⟨fun a ha => ?_, (holds_cpnG h t b).1 hguard⟩
    obtain ⟨hain, hat⟩ := List.mem_filter.1 ha
    obtain ⟨p, hp, rfl⟩ := exists_cpnInArc h hain t (by simpa using hat)
    intro v
    by_cases hv : v.ofColor (N.arcOfIn (p, t) hp).color = true
    · have hvw : v.ofColor (N.placeAt p).color = true := by
        rwa [N.arcOfIn_color h (p, t) hp] at hv
      rw [(N.arcOfIn_names (p, t) hp).1]
      calc (Expr.eval (N.arcOfIn (p, t) hp).expr b').coeff v
          = CPN.consumedBy b p hp ⟨v, hvw⟩ := (consumedBy_coeff h t b p hp ⟨v, hvw⟩).symm
        _ ≤ d p ⟨v, hvw⟩ := hpre p hp ⟨v, hvw⟩
        _ = (M (N.placeAt p).name).coeff v := hR p ⟨v, hvw⟩
    · rw [coeff_eval_eq_zero hwf
        (fun q hq => N.mem_Var_of_pre (N.arcOfIn_mem_pre hp) hq) hv]
      exact Nat.zero_le _
  · rintro ⟨hpre, hguard⟩
    refine ⟨fun p hp v => ?_, (holds_cpnG h t b).2 hguard⟩
    calc CPN.consumedBy b p hp v
        = (Expr.eval (N.arcOfIn (p, t) hp).expr b').coeff v.1 :=
          consumedBy_coeff h t b p hp v
      _ ≤ (M (N.arcOfIn (p, t) hp).place).coeff v.1 :=
          hpre _ (N.arcOfIn_mem_pre hp) v.1
      _ = (M (N.placeAt p).name).coeff v.1 := by rw [(N.arcOfIn_names (p, t) hp).1]
      _ = d p v := (hR p v).symm

/-! ## Definition 7 -/

theorem consume_coeff {N : Net} (h : N.Valid) (t : N.TIdx) (b : (N.toCPN h).TransBinding t)
    (p : N.PIdx) (v : Bridge.Val (N.placeAt p).color) :
    CPN.consume b p v =
      (N.consume (N.transAt t).name (envOfTransBinding h t b) (N.placeAt p).name).coeff v.1 := by
  by_cases hp : (p, t) ∈ N.cpnInArc
  · have hcons : CPN.consume b p = CPN.consumedBy b p hp := by
      simp only [CPN.consume]
      exact dite_eq_left hp
    rw [hcons, consumedBy_coeff h t b p hp]
    show _ = (match N.inArc? (N.placeAt p).name (N.transAt t).name with
      | some a => Expr.eval a.expr (envOfTransBinding h t b)
      | none => ∅).coeff v.1
    rw [N.inArc?_arcOfIn (p, t) hp]
  · have hnone : N.inArc? (N.placeAt p).name (N.transAt t).name = none :=
      Option.not_isSome_iff_eq_none.1 (by simpa [cpnInArc] using hp)
    have hcons : CPN.consume b p = ∅ := by
      simp only [CPN.consume]
      exact dite_eq_right hp
    rw [hcons]
    show (0 : ℕ) = (match N.inArc? (N.placeAt p).name (N.transAt t).name with
      | some a => Expr.eval a.expr (envOfTransBinding h t b)
      | none => ∅).coeff v.1
    rw [hnone]
    rfl

theorem produce_coeff {N : Net} (h : N.Valid) (t : N.TIdx) (b : (N.toCPN h).TransBinding t)
    (p : N.PIdx) (v : Bridge.Val (N.placeAt p).color) :
    CPN.produce b p v =
      (N.produce (N.transAt t).name (envOfTransBinding h t b) (N.placeAt p).name).coeff v.1 := by
  by_cases hp : (t, p) ∈ N.cpnOutArc
  · have hprod : CPN.produce b p = CPN.producedBy b p hp := by
      simp only [CPN.produce]
      exact dite_eq_left hp
    rw [hprod, producedBy_coeff h t b p hp]
    show _ = (match N.outArc? (N.transAt t).name (N.placeAt p).name with
      | some a => Expr.eval a.expr (envOfTransBinding h t b)
      | none => ∅).coeff v.1
    rw [N.outArc?_arcOfOut (t, p) hp]
  · have hnone : N.outArc? (N.transAt t).name (N.placeAt p).name = none :=
      Option.not_isSome_iff_eq_none.1 (by simpa [cpnOutArc] using hp)
    have hprod : CPN.produce b p = ∅ := by
      simp only [CPN.produce]
      exact dite_eq_right hp
    rw [hprod]
    show (0 : ℕ) = (match N.outArc? (N.transAt t).name (N.placeAt p).name with
      | some a => Expr.eval a.expr (envOfTransBinding h t b)
      | none => ∅).coeff v.1
    rw [hnone]
    rfl

/-- **Definition 7, on both sides.** -/
theorem cpnFire_coeff {N : Net} (h : N.Valid) (t : N.TIdx) (d : (N.toCPN h).Marking)
    (M : Marking) (hR : markingRel h d M) (b : (N.toCPN h).TransBinding t) :
    markingRel h (CPN.fire d b) (N.fire M (N.transAt t) (envOfTransBinding h t b)) := by
  intro p v
  show (d p v - CPN.consume b p v) + CPN.produce b p v
      = ((M (N.placeAt p).name \ N.consume (N.transAt t).name (envOfTransBinding h t b)
            (N.placeAt p).name)
          ∪ N.produce (N.transAt t).name (envOfTransBinding h t b) (N.placeAt p).name).coeff v.1
  rw [Bag.coeff_union, Bag.coeff_diff, hR p v, consume_coeff h t b p v,
    produce_coeff h t b p v]

end Net

end Cpn2mCrl2
