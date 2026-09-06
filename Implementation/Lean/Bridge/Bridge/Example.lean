/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Bridge.ListSoundness
import Cpn2mCrl2.Examples.Counter

/-!
# The whole chain, on Example 3

`Examples/Counter.lean` builds the counter net, checks Examples 4 and 5 on it by evaluation,
and checks the emitted text character for character. This file adds the last statement, which
needs `Proof/` and so cannot live there: the reachability graph of Definition 9 for that net
and the LTS of the specification the translator prints for it are bisimilar.

Everything it rests on is discharged rather than assumed. `net_valid` is decided;
`Net.bisimilar_reachabilityGraph_emitted` is tier T2 composed with Theorem 1.
-/

namespace Cpn2mCrl2.Examples.Counter

/-- **Example 3, end to end.**
The reachability graph of the counter net -- Example 5, the corrected seven-state chain -- and
the LTS of the mCRL2 specification `net.toMcrl2` prints for it are bisimilar. -/
theorem bisimilar_emitted :
    LTS.Bisimilar (net.toCPN net_valid).reachabilityGraph net.emittedLTS :=
  Net.bisimilar_reachabilityGraph_emitted net_valid

/-- **The same for the fast backend.**
The list-encoded specification `net.toMcrl2List` prints denotes an LTS bisimilar to the same
reachability graph. -/
theorem bisimilar_emittedList :
    LTS.Bisimilar (net.toCPN net_valid).reachabilityGraph net.emittedListLTS :=
  Net.bisimilar_reachabilityGraph_emittedList net_valid

end Cpn2mCrl2.Examples.Counter
