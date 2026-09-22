/-
Asserts what `Proof/README.md` and `Thesis/docs/LeanFormalization.md` §1.1 claim about this
package: that the soundness theorem and the results it rests on are proved outright, from
Lean's three standard axioms and nothing else.

Not part of either default target — it is run on its own by `.github/scripts/check-lean-proved.sh`,
which reads the `#print axioms` lines below and fails on any axiom outside the allowed set. An
unproved declaration anywhere beneath one of these theorems surfaces here as `sorryAx`.

The word this file is guarding against is deliberately never spelled in it: the workflow's
other Lean check is a blunt grep over every tracked `.lean` source, with no exceptions.
-/
import Proof

#print axioms CPN.bisimulation_transRel
#print axioms CPN.bisimilar_toLPESemantics
#print axioms CPN.mem_RGState_of_directlyReachable
#print axioms CPN.toLPE_cond
#print axioms CPN.toLPE_next
