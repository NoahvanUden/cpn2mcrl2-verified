/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Bridge.Soundness

/-!
# The list backend, composed with Theorem 1

`Cpn2mCrl2/ListEncoding.lean` proves the refinement of `Implementation/docs/Plan.md` §5 as two
implications between step relations, because the main package has no `LTS` -- that lives in
`Proof/`. This file packages them as one `LTS.Bisimulation` and composes with
`Net.bisimilar_reachabilityGraph_emitted`.

The result is that the *fast* backend has exactly the justification the slow one has.
`Plan.md` §5 says of the list encoding as things stood:

> Until that lemma exists, the fast output is exactly as justified as the reference implementation's, which is to say not at all.

The lemma exists.

## The order problem, concretely

`fixtures/multitoken.cpn.json` is the net `Implementation/docs/Target.md` §4.1 asks for. Run
through the toolset, the two backends give

```
bag encoding    des (0,4,4)
list encoding   des (0,4,5)
```

-- four states against five, because the list encoding reaches `[1,2]` and `[2,1]` as distinct
states where the bag encoding reaches one marking. `ltscompare -ebisim` reports them equal
anyway. That is `Plan.md` §5's prediction observed:

> Those states should be bisimilar, but they are not equal — so the induced LTS has strictly more states than the reachability graph, and bisimilarity holds where isomorphism fails.

## Main results

* `Net.bisimulation_listRel` : the two backends are bisimilar.
* `Net.bisimilar_reachabilityGraph_emittedList` : and so the list backend is bisimilar to the
  reachability graph of Definition 9.
-/

namespace Cpn2mCrl2

namespace Net

/-- The transition system the list-encoded specification denotes, over the same actions as
`Net.emittedLTS`. -/
def emittedListLTS (N : Net) : LTS ListMarking N.TIdx where
  step LM t LM' := N.toLpeList.step LM (N.transAt t).name LM'
  init := N.toLpeList.initMarking

@[simp] theorem emittedListLTS_step (N : Net) (LM : ListMarking) (t : N.TIdx)
    (LM' : ListMarking) :
    N.emittedListLTS.step LM t LM' ↔ N.toLpeList.step LM (N.transAt t).name LM' := Iff.rfl

@[simp] theorem emittedListLTS_init (N : Net) :
    N.emittedListLTS.init = N.toLpeList.initMarking := rfl

/-- **The two backends are bisimilar**, related by "these markings represent the same bags".

Both halves are `Cpn2mCrl2/ListEncoding.lean`'s; all this does is name them as the two
conditions of Definition 16. -/
theorem bisimulation_listRel {N : Net} (h : N.Valid) :
    LTS.Bisimulation N.emittedListLTS N.emittedLTS listRel := by
  constructor
  · rintro LM M LM' t hstep hR
    exact step_of_toLpeList_step h hR hstep
  · rintro LM M M' t hstep hR
    exact toLpeList_step_of_step h hR hstep

theorem bisimilar_emittedListLTS {N : Net} (h : N.Valid) :
    LTS.Bisimilar N.emittedListLTS N.emittedLTS :=
  ⟨listRel, bisimulation_listRel h, listRel_init h⟩

/-- **The fast backend, all the way back to Definition 9.**

For a CPN that passes the T1 validation, the reachability graph and the LTS denoted by the
*list-encoded* specification the translator emits are bisimilar. Milestone M6 of
`Implementation/docs/Plan.md`, composed with Theorem 1. -/
theorem bisimilar_reachabilityGraph_emittedList {N : Net} (h : N.Valid) :
    LTS.Bisimilar (N.toCPN h).reachabilityGraph N.emittedListLTS :=
  (bisimilar_reachabilityGraph_emitted h).trans (bisimilar_emittedListLTS h).symm

end Net

end Cpn2mCrl2
