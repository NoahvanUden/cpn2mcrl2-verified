/-
Asserts the axiom claim of `Implementation/Lean/README.md` for the composed theorems — the ones
that carry the whole claim, since each puts Theorem 1 of `Proof/` and T2 of the translator on
either side of a bisimulation. Run by `.github/scripts/check-lean-proved.sh`; see
`Proof/scripts/Axioms.lean`.
-/
import Bridge

#print axioms Cpn2mCrl2.Net.bisimilar_reachabilityGraph_emitted
#print axioms Cpn2mCrl2.Net.bisimilar_reachabilityGraph_emittedList
#print axioms Cpn2mCrl2.Examples.Counter.bisimilar_emitted
#print axioms Cpn2mCrl2.Examples.Counter.bisimilar_emittedList
