/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Proof.Bisimulation
import Proof.MCRL2

/-!
# A CPN and its translation are bisimilar

Definition 17 and Theorem 1 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025), Section 5.3: the relation between the reachability graph of a CPN
(Definition 9) and the LTS induced by the LPE it is translated into (Definitions 14 and 15),
and the theorem that it is a bisimulation.

See `Thesis/docs/Bisimiliarity.md` for the prose version, including the six places where the
printed proof states a condition over the wrong set of places.

## Why the proof is short here

The thesis proves Theorem 1 by unfolding both sides: the CPN side gives a guard and an
inclusion per place of the preset, the LPE side gives the condition `c_t` and the next state
`g_t` of the summand of `t`, and the two are compared component by component. Most of that
bookkeeping is discharged by how `CPN.toLPE` represents the state and the summation
variable: Definition 14 defines `D` as the tuple holding one bag of tokens per place, which
is a marking, and `H_t` as the tuple of values of the variables of `t`, which is a binding of
`Var(t)`. Representing those tuples by the marking and the binding they are indexed by lines
the two sides up component by component with nothing left to say.

The comparison itself is still made, and not assumed: `CPN.toLPE` builds `c_t` and `g_t` from
Definition 14's text rather than reusing `Enabled` and `fire`, and `CPN.toLPE_cond` and
`CPN.toLPE_next` are what identify the two. Both hold by `rfl` -- the two are transcriptions
of one formula -- but they are claims that stop typechecking if either side drifts, which is
what keeps this theorem from being a statement about a single object under two names.

What is left is the part of the proof that is not bookkeeping: the two LTSs do not have the
same states. The reachability graph is restricted to `{M₀} ∪ R(M₀)` while the induced LTS
has every element of `D` as a state, so the LPE step has to be shown to land back in the
reachable part -- which is `CPN.mem_RGState_of_directlyReachable`.
-/

universe u v w x y

namespace CPN

variable {L : ExprLang.{u, v, w, x}} {P T : Type y} (N : CPN L P T)

/-- **Definition 17.**
The relation between the reachability graph of a CPN and the LTS induced by the LPE it
translates to: a marking `M` is related to the state `(M(p₁), …, M(pₙ))` of the LPE that
stores, for each place, the bag of tokens `M` assigns to it.

That tuple is `M` itself here, because Definition 14 represents the state of the LPE by the
marking it consists of, so the relation is "the state of the LPE is the marking". -/
def transRel : N.RGState → N.Marking → Prop := fun M d => M.1 = d

/-- **Theorem 1.**
The relation of Definition 17 is a bisimulation relation between the reachability graph of a
CPN and the LTS induced by its translation. -/
theorem bisimulation_transRel :
    LTS.Bisimulation N.reachabilityGraph N.toLPESemantics (transRel N) := by
  constructor
  -- Condition 1: a step of the CPN is matched by the LPE, on the same marking.
  · rintro M d M' t hstep rfl
    exact ⟨M'.1, (N.toLPESemantics_step _ _ _).2 hstep, rfl⟩
  -- Condition 2: a step of the LPE is matched by the CPN. The marking it reaches is
  -- reachable, since the marking it starts from is, so it is a state of the reachability
  -- graph.
  · rintro M d d' t hstep rfl
    obtain ⟨b, hocc⟩ := (N.toLPESemantics_step _ _ _).1 hstep
    exact ⟨⟨d', N.mem_RGState_of_directlyReachable M.2 ⟨t, b, hocc⟩⟩, ⟨b, hocc⟩, rfl⟩

/-- The reachability graph of a CPN and the LTS induced by the LPE it is translated into are
bisimilar: their initial states are both the initial marking, and they are related by the
bisimulation of Theorem 1.

This is what makes the translation usable as a verification back-end: the behavior of the
CPN model and of the mCRL2 specification is the same, so a property holds of one if and only
if it holds of the other. -/
theorem bisimilar_toLPESemantics :
    LTS.Bisimilar N.reachabilityGraph N.toLPESemantics :=
  ⟨transRel N, bisimulation_transRel N, rfl⟩

end CPN
