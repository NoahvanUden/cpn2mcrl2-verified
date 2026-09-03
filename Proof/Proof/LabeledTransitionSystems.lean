/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Mathlib.Logic.Relation

/-!
# Labeled Transition Systems

Definition 3 of the thesis *Model checking for analysis of BPMN models*
(N. van Uden, TU/e, 2025), Chapter 2 (*Mathematical preliminaries*).

See `Thesis/docs/LabeledTransitionSystems.md` for the prose version of this definition.

The LTS is the common semantic domain of the project: the reachability graph of a Colored
Petri Net (Definition 9) is an LTS, and the LTS induced by an mCRL2 Linear Process Equation
(Definition 15) is an LTS. Bisimilarity (Definitions 16-17) is stated between two of them.

## Implementation notes

The thesis writes an LTS as a four tuple `(S, L, →, s₀)`, in which `S` and `L` are
*possibly infinite* sets. They are therefore modelled as Lean types rather than as
`Set`s of some ambient type, and they are parameters of `LTS` rather than fields of it:
Definition 16 relates two LTSs whose state and action types differ, so keeping them
visible in the type is what lets that definition be stated later.

The transition relation `→ ⊆ S × L × S` is modelled in curried form as
`S → L → S → Prop`, which carries the same information as `Set (S × L × S)`.

## Main definitions

* `LTS S L` : a labeled transition system with states `S` and actions `L`.
* `LTS.Reaches` : the reflexive-transitive closure of the transition relation.
* `LTS.Reachable` : the states reachable from the initial state.
-/

universe u v

/-- **Definition 3 (Labeled Transition System (LTS)).**
A Labeled Transition System is a four tuple `(S, L, →, s₀)` where `S` is a possibly
infinite set of states, `L` is a possibly infinite set of actions,
`→ ⊆ S × L × S` is a transition relation, and `s₀ ∈ S` is the initial state.

Here the state set `S` and the action set `L` are the parameters of the structure, so an
`LTS S L` bundles the remaining two components: the transition relation and the initial
state. -/
structure LTS (S : Type u) (L : Type v) where
  /-- The transition relation `→ ⊆ S × L × S`, in curried form: `step s t s'` holds
  exactly when `(s, t, s') ∈ →`, written `s -t→ s'` in the thesis. -/
  step : S → L → S → Prop
  /-- The initial state `s₀ ∈ S`. -/
  init : S

namespace LTS

variable {S : Type u} {L : Type v}

/-- Notation for a transition `s -t→ s'` of the LTS `M`, i.e. `(s, t, s') ∈ →`.
The thesis writes this as `s -t→ s'`, leaving the LTS implicit in the context. -/
scoped notation:50 M " ⊢ " s:51 " -[" t "]→ " s':51 => LTS.step M s t s'

/-! ### Paths

Definition 3 fixes only the syntax above. The behavior an LTS describes is the set of
paths through the graph starting from `s₀`; the following two definitions name that,
and are not themselves part of Definition 3. -/

/-- `M.Reaches s s'` holds when `s'` can be reached from `s` by a finite (possibly empty)
sequence of transitions of `M`, of any actions. -/
def Reaches (M : LTS S L) : S → S → Prop :=
  Relation.ReflTransGen fun s s' => ∃ t, M ⊢ s -[t]→ s'

/-- A state is reachable when it lies on a path from the initial state `s₀`. -/
def Reachable (M : LTS S L) (s : S) : Prop :=
  M.Reaches M.init s

theorem reachable_init (M : LTS S L) : M.Reachable M.init :=
  Relation.ReflTransGen.refl

theorem Reaches.single {M : LTS S L} {s s' : S} {t : L} (h : M ⊢ s -[t]→ s') :
    M.Reaches s s' :=
  Relation.ReflTransGen.single ⟨t, h⟩

theorem Reaches.trans {M : LTS S L} {s s' s'' : S} (h : M.Reaches s s')
    (h' : M.Reaches s' s'') : M.Reaches s s'' :=
  Relation.ReflTransGen.trans h h'

/-- A state reached from a reachable state is itself reachable. -/
theorem Reachable.step {M : LTS S L} {s s' : S} {t : L} (hs : M.Reachable s)
    (h : M ⊢ s -[t]→ s') : M.Reachable s' :=
  Relation.ReflTransGen.tail hs ⟨t, h⟩

end LTS
