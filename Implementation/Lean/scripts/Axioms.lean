/-
Asserts the axiom claim of `Implementation/Lean/README.md` for the T2 theorems: the emitted
condition and next-state terms denote Definition 14, and the two transition relations agree.
Run by `.github/scripts/check-lean-proved.sh`; see `Proof/scripts/Axioms.lean`, including its note
on why the word being guarded against is not written here.

`toLpe_cond` reports fewer than three axioms, which is why the checker allows a subset of the
standard three rather than demanding all of them.
-/
import Cpn2mCrl2.Correct

#print axioms Cpn2mCrl2.Net.toLpe_cond
#print axioms Cpn2mCrl2.Net.toLpe_next
#print axioms Cpn2mCrl2.Net.toLpe_step
