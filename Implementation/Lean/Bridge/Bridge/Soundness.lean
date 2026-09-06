/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Bridge.Semantics

/-!
# T2 composed with Theorem 1

The theorem `Implementation/docs/Plan.md` §2 says the project is for:

> **T2 composed with T3 is the theorem the project is for**: *the specification this program prints denotes an LTS bisimilar to the CPN's reachability graph.* T3 is done. T2 is the work.

T2 is `Cpn2mCrl2/Correct.lean`, T3 is `CPN.bisimulation_transRel` of `Proof/Soundness.lean`,
and this file composes them. `Implementation/Lean/README.md` recorded the composition as
holding mathematically but not mechanically; `Net.bisimilar_reachabilityGraph_emitted` is it,
mechanically.

## What the statement says, and what it does not

`Net.emittedLTS` is the transition system the *emitted specification* denotes: its steps are
`Lpe.step` of `Net.toLpe`, the object `Cpn2mCrl2/Print.lean` prints. So the theorem reads: for
a CPN that passes the T1 validation, the reachability graph of Definition 9 and the LTS of the
specification the translator emits are bisimilar.

It stops one link short of the text, and deliberately. Tier T4 -- that `mcrl22lps` reads the
printed characters back as the term that was printed -- is not provable without a formalized
mCRL2 grammar, and `Implementation/docs/Plan.md` §2 rules it out of scope. `scripts/check.sh`
tests it.

## Main results

* `Net.bisimulation_markingRel` : the emitted LPE and `Proof/`'s induced LTS are bisimilar.
* `Net.bisimilar_reachabilityGraph_emitted` : composed with Theorem 1.
-/

namespace Cpn2mCrl2

namespace Net

/-! ## A transition is determined by its name -/

theorem find?_trans_of_mem : ∀ {l : List TransDecl}, ListUtil.NoDup (l.map TransDecl.name) →
    ∀ {d : TransDecl}, d ∈ l → l.find? (fun e => e.name == d.name) = some d := by
  intro l
  induction l with
  | nil => intro _ d hd; cases hd
  | cons e tl ih =>
    intro hnd d hd
    by_cases he : e.name = d.name
    · have hed : e = d := by
        rcases List.mem_cons.1 hd with hq | hq
        · exact hq.symm
        · exact absurd (he ▸ List.mem_map_of_mem (f := TransDecl.name) hq) hnd.1
      exact (List.find?_cons_of_pos (by simp [he])).trans (by rw [hed])
    · have hdt : d ∈ tl := by
        rcases List.mem_cons.1 hd with hq | hq
        · exact absurd (congrArg TransDecl.name hq.symm) he
        · exact hq
      exact (List.find?_cons_of_neg (by simp [he])).trans (ih hnd.2 hdt)

theorem trans_eq_of_name {N : Net} (h : N.Valid) {t₁ t₂ : TransDecl} (h₁ : t₁ ∈ N.transitions)
    (h₂ : t₂ ∈ N.transitions) (hn : t₁.name = t₂.name) : t₁ = t₂ := by
  have e₁ := find?_trans_of_mem h.transNodup h₁
  have e₂ := find?_trans_of_mem h.transNodup h₂
  rw [hn] at e₁
  exact Option.some.inj (e₁.symm.trans e₂)

/-! ## The round trip on bindings

Reading one of our environments as a binding of `Proof/` and back changes nothing that an
expression of the transition can see. This is `Expr.eval_congr` again -- obligation 4 of
`Implementation/docs/Plan.md` §4 -- and it is the last place it is needed. -/

theorem eval_transBindingOfEnv {N : Net} (h : N.Valid) (t : N.TIdx) (b : Env)
    (hb : b.WfOn (N.Var (N.transAt t))) {ρ : ExprTy} (e : Expr ρ)
    (hs : ∀ q ∈ e.freeVars, q ∈ N.Var (N.transAt t)) :
    Expr.eval e (envOfTransBinding h t (transBindingOfEnv h t b hb)) = Expr.eval e b := by
  refine Expr.eval_congr e ?_
  rintro ⟨x, σ⟩ hx
  have hmem := hs _ hx
  have hσ : σ = ExprTy.color (N.varTypeOf x) :=
    Net.varTypeOf_of_mem h (Var_subset_vars h (N.transAt_mem t) hmem)
  subst hσ
  have hxv : x ∈ (N.toCPN h).Var t := mem_cpnVar_of_mem_Var h t hmem
  show Bridge.envOfBinding N ((N.toCPN h).Var t) (transBindingOfEnv h t b hb)
      (.color (N.varTypeOf x)) x = _
  rw [Bridge.envOfBinding_color (transBindingOfEnv h t b hb) hxv]
  rfl

theorem enabled_transBindingOfEnv {N : Net} (h : N.Valid) (t : N.TIdx) (M : Marking)
    (b : Env) (hb : b.WfOn (N.Var (N.transAt t))) :
    N.Enabled M (N.transAt t) (envOfTransBinding h t (transBindingOfEnv h t b hb))
      ↔ N.Enabled M (N.transAt t) b := by
  unfold Net.Enabled Expr.Holds
  rw [eval_transBindingOfEnv h t b hb (N.transAt t).guard
    (fun q hq => N.mem_Var_of_guard hq)]
  refine and_congr_left fun _ => ?_
  constructor <;> intro hpre a ha <;>
    [rw [← eval_transBindingOfEnv h t b hb a.expr (fun q hq => N.mem_Var_of_pre ha hq)];
     rw [eval_transBindingOfEnv h t b hb a.expr (fun q hq => N.mem_Var_of_pre ha hq)]] <;>
    exact hpre a ha

theorem consume_transBindingOfEnv {N : Net} (h : N.Valid) (t : N.TIdx) (b : Env)
    (hb : b.WfOn (N.Var (N.transAt t))) (p : String) :
    N.consume (N.transAt t).name (envOfTransBinding h t (transBindingOfEnv h t b hb)) p
      = N.consume (N.transAt t).name b p := by
  unfold Net.consume
  cases hf : N.inArc? p (N.transAt t).name with
  | none => rfl
  | some a =>
    have hpred := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    have ha : a ∈ N.pre (N.transAt t).name :=
      List.mem_filter.2 ⟨List.mem_of_find?_eq_some hf, by simp [hpred.2]⟩
    exact eval_transBindingOfEnv h t b hb a.expr (fun q hq => N.mem_Var_of_pre ha hq)

theorem produce_transBindingOfEnv {N : Net} (h : N.Valid) (t : N.TIdx) (b : Env)
    (hb : b.WfOn (N.Var (N.transAt t))) (p : String) :
    N.produce (N.transAt t).name (envOfTransBinding h t (transBindingOfEnv h t b hb)) p
      = N.produce (N.transAt t).name b p := by
  unfold Net.produce
  cases hf : N.outArc? (N.transAt t).name p with
  | none => rfl
  | some a =>
    have hpred := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    have ha : a ∈ N.post (N.transAt t).name :=
      List.mem_filter.2 ⟨List.mem_of_find?_eq_some hf, by simp [hpred.2]⟩
    exact eval_transBindingOfEnv h t b hb a.expr (fun q hq => N.mem_Var_of_post ha hq)

theorem fire_transBindingOfEnv {N : Net} (h : N.Valid) (t : N.TIdx) (M : Marking) (b : Env)
    (hb : b.WfOn (N.Var (N.transAt t))) (p : String) :
    N.fire M (N.transAt t) (envOfTransBinding h t (transBindingOfEnv h t b hb)) p
      = N.fire M (N.transAt t) b p := by
  unfold Net.fire
  rw [consume_transBindingOfEnv h t b hb p, produce_transBindingOfEnv h t b hb p]

/-! ## The LTS the emitted specification denotes -/

/-- The transition system of the specification the translator prints.

Its actions are the transitions of the net rather than their names, which is what lets it be
compared with `Proof/`'s LTS: `LTS.Bisimulation` relates two systems over *one* action type.
Nothing is lost -- `Net.Valid.transNodup` makes the name determine the transition. -/
def emittedLTS (N : Net) : LTS Marking N.TIdx where
  step M t M' := N.toLpe.step M (N.transAt t).name M'
  init := N.toLpe.initMarking

@[simp] theorem emittedLTS_step (N : Net) (M : Marking) (t : N.TIdx) (M' : Marking) :
    N.emittedLTS.step M t M' ↔ N.toLpe.step M (N.transAt t).name M' := Iff.rfl

@[simp] theorem emittedLTS_init (N : Net) : N.emittedLTS.init = N.toLpe.initMarking := rfl

/-! ## The initial states -/

theorem markingRel_init {N : Net} (h : N.Valid) :
    markingRel h (N.toCPN h).toLPEInit N.toLpe.initMarking := by
  intro p v
  have hlk : List.lookup (N.placeAt p).name N.toLpe.init
      = some ⟨(N.placeAt p).color, (N.placeAt p).init⟩ :=
    lookup_name_of_mem (fun d => (⟨d.color, d.init⟩ : BagTerm)) h.placesNodup (N.placeAt_mem p)
  have hinit : N.toLpe.initMarking (N.placeAt p).name
      = Expr.eval (N.placeAt p).init Env.junk := by
    simp only [Lpe.initMarking, hlk]
  rw [hinit]
  refine congrArg (fun m : Bag => m.coeff v.1) (Expr.eval_congr _ ?_)
  intro q hq
  have hf : q ∈ (N.placeAt p).init.freeVars := hq
  rw [h.initClosed _ (N.placeAt_mem p)] at hf
  cases hf

/-! ## The bisimulation -/

/-- The LTS `Proof/` induces from the translated LPE and the LTS the emitted specification
denotes are bisimilar, related by "the two markings give every well-typed token the same
coefficient". -/
theorem bisimulation_markingRel {N : Net} (h : N.Valid) :
    LTS.Bisimulation (N.toCPN h).toLPESemantics N.emittedLTS (markingRel h) := by
  constructor
  · rintro d M d' t hstep hR
    obtain ⟨b, hen, rfl⟩ := ((N.toCPN h).toLPESemantics_step d t d').1 hstep
    refine ⟨N.fire M (N.transAt t) (envOfTransBinding h t b), ?_,
      cpnFire_coeff h t d M hR b⟩
    refine (N.toLpe_step h M (N.transAt t).name _).2 ⟨N.transAt t, N.transAt_mem t, rfl,
      envOfTransBinding h t b, wfOn_envOfTransBinding h t b, ?_, fun p => Bag.Equiv.rfl _⟩
    exact (cpnEnabled_iff h t d M hR b).1 hen
  · rintro d M M' t hstep hR
    obtain ⟨td, htd, hname, bb, hbb, hen, hnext⟩ :=
      (N.toLpe_step h M (N.transAt t).name M').1 hstep
    have htd' : td = N.transAt t := trans_eq_of_name h htd (N.transAt_mem t) hname
    subst htd'
    refine ⟨CPN.fire d (transBindingOfEnv h t bb hbb),
      ((N.toCPN h).toLPESemantics_step d t _).2
        ⟨transBindingOfEnv h t bb hbb, ?_, rfl⟩, ?_⟩
    · exact (cpnEnabled_iff h t d M hR _).2
        ((enabled_transBindingOfEnv h t M bb hbb).2 hen)
    · intro p v
      rw [cpnFire_coeff h t d M hR (transBindingOfEnv h t bb hbb) p v,
        fire_transBindingOfEnv h t M bb hbb (N.placeAt p).name, ← hnext (N.placeAt p).name v.1]

/-- The two are bisimilar as systems: their initial states are related. -/
theorem bisimilar_toLPESemantics_emitted {N : Net} (h : N.Valid) :
    LTS.Bisimilar (N.toCPN h).toLPESemantics N.emittedLTS :=
  ⟨markingRel h, bisimulation_markingRel h, markingRel_init h⟩

/-- **T2 composed with Theorem 1.**

For a CPN that passes the T1 validation of `Implementation/docs/InputFormat.md` §4.3, the
reachability graph of Definition 9 and the LTS denoted by the mCRL2 specification the
translator emits are bisimilar.

The left-hand side is `Proof/`'s, unchanged, and the right-hand side is the denotation of
`Net.toLpe` -- the object `Cpn2mCrl2/Print.lean` prints. Between them stand
`CPN.bisimulation_transRel`, which is Theorem 1 of the thesis, and `Net.toLpe_step`, which is
tier T2. -/
theorem bisimilar_reachabilityGraph_emitted {N : Net} (h : N.Valid) :
    LTS.Bisimilar (N.toCPN h).reachabilityGraph N.emittedLTS :=
  ((N.toCPN h).bisimilar_toLPESemantics).trans (bisimilar_toLPESemantics_emitted h)

end Net

end Cpn2mCrl2
