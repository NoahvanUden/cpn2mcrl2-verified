/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2.Expr

/-!
# Type soundness

`Expr` is indexed by `ExprTy`, so a guard is a boolean expression and an arc expression is a
bag expression by construction. `Value`, on the other hand, is untyped -- see the
implementation notes of `Cpn2mCrl2/Color.lean` for why -- so nothing about the *index* of an
expression is, so far, a claim about the value it evaluates to. `Expr.eval` even has cases
that cannot arise: `Value.asInt` of something that is not an integer, and the projection of a
field a record value does not carry, which falls back on `Color.junk`.

This file closes that. `Expr.eval_wf` says that under a well-typed environment an expression
of sort `τ` evaluates to a value of sort `τ`, so `Color.junk` is never reached and `asInt`,
`asBool` and `asRecord` always read a value that is really of that shape.

Nothing in `Cpn2mCrl2/Correct.lean` depends on it. The T2 theorems compare two uses of the
same `eval`, so junk on one side is junk on the other and the identity holds either way. What
this adds is the reason to believe `eval` is the semantics it is meant to be, rather than a
function that happens to satisfy an equation.

## Main results

* `Expr.eval_wf` : evaluation preserves sorts.
* `Expr.eval_ofColor`, `Expr.eval_bag_ofColor` : the same, spelled out at each sort.
-/

namespace Cpn2mCrl2

namespace Expr

mutual

/-- Under an environment well-typed on its free variables, an expression of sort `τ`
evaluates to a value of sort `τ`.

The hypothesis is `Env.WfOn e.freeVars` rather than `Env.Wf` because `Env.Wf` is too strong to
be satisfiable: `Env` is total, and an enumeration with no constructors has no value for the
junk environment to hold. `Cpn2mCrl2/Bridge` needs exactly this form, since a binding of
Definition 2 constrains only the variables it binds. -/
theorem eval_wf : ∀ {τ : ExprTy} (e : Expr τ) {env : Env}, env.WfOn e.freeVars →
    τ.Wf (eval e env)
  | _, .var x τ, _, h => h (x, τ) (List.mem_singleton.2 rfl)
  | _, .intLit _, _, _ => rfl
  | _, .boolLit _, _, _ => rfl
  | _, .ctorLit _ _ _ hm, _, _ => by
      show decide (_ ∈ _) = true
      exact decide_eq_true hm
  | _, .mkRec _ args, _, h => Args.eval_wf args h
  | _, .proj e f c hf, _, h => by
      obtain ⟨vs, hv, hvs⟩ := Value.eq_record_of_ofColor (eval_wf e h)
      obtain ⟨w, hw, hwc⟩ := ValueFields.lookup_ofColorFields hvs hf
      show Value.ofColor (((eval e _).asRecord.lookup f).getD c.junk) c = true
      rw [hv]
      show Value.ofColor ((vs.lookup f).getD c.junk) c = true
      rw [hw]
      exact hwc
  | _, .add _ _, _, _ => rfl
  | _, .sub _ _, _, _ => rfl
  | _, .mul _ _, _, _ => rfl
  | _, .eq _ _, _, _ => rfl
  | _, .le _ _, _, _ => rfl
  | _, .lt _ _, _, _ => rfl
  | _, .and _ _, _, _ => rfl
  | _, .or _ _, _, _ => rfl
  | _, .not _, _, _ => rfl
  | _, .bagSubset _ _, _, _ => rfl
  | _, .emptyBag _, _, _ => rfl
  | _, .single _ e, _, h => by
      have he := eval_wf e h
      show Bag.ofColor (Bag.single _ (eval e _)) _ = true
      simp only [Bag.ofColor, Bag.single, List.all_cons, List.all_nil, Bool.and_true]
      exact he
  | _, .bagUnion a b, _, h => by
      show Bag.ofColor (eval a _ ∪ eval b _) _ = true
      have ha := eval_wf a fun p hp => h p (List.mem_append_left _ hp)
      have hb := eval_wf b fun p hp => h p (List.mem_append_right _ hp)
      simp only [Bag.ofColor, Union.union, Bag.union, List.all_append, Bool.and_eq_true]
      exact ⟨ha, hb⟩
  | _, .bagDiff a b, _, h => by
      have ha := eval_wf a fun p hp => h p (List.mem_append_left _ hp)
      show Bag.ofColor (eval a _ \ eval b _) _ = true
      simp only [Bag.ofColor, SDiff.sdiff, Bag.diff, List.all_eq_true, List.mem_map]
      rintro e ⟨v, hv, rfl⟩
      have : v ∈ (eval a _ : Bag).entries.map Prod.fst := ListUtil.mem_dedup.1 hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 this
      exact List.all_eq_true.1 ha p hp

/-- `Expr.eval_wf`, one record field at a time. -/
theorem Args.eval_wf : ∀ {fs : ColorFields} (args : Args fs) {env : Env},
    env.WfOn (Args.freeVars args) → ValueFields.ofColorFields (Args.eval args env) fs = true
  | _, .nil, _, _ => rfl
  | _, .cons e rest, _, h => by
      show ValueFields.ofColorFields (.cons _ (eval e _) (Args.eval rest _)) (.cons _ _ _) = true
      simp only [ValueFields.ofColorFields, Bool.and_eq_true, beq_self_eq_true, true_and]
      exact ⟨eval_wf e fun p hp => h p (List.mem_append_left _ hp),
        Args.eval_wf rest fun p hp => h p (List.mem_append_right _ hp)⟩

end

/-- Evaluation at a color sort: the value really is of that color, so `Value.asInt`,
`Value.asBool` and `Value.asRecord` never fall back. -/
theorem eval_ofColor {c : Color} (e : Expr (.color c)) {env : Env}
    (h : env.WfOn e.freeVars) : (eval e env).ofColor c = true := eval_wf e h

/-- Evaluation at a bag sort: every item of the bag is of the color. -/
theorem eval_bag_ofColor {c : Color} (e : Expr (.bag c)) {env : Env}
    (h : env.WfOn e.freeVars) : (eval e env).ofColor c = true := eval_wf e h

end Expr

end Cpn2mCrl2
