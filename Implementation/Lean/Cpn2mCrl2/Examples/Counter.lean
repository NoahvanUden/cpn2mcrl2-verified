/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2

/-!
# Examples 3, 4, 5 and 9

The counter net, built directly in Lean rather than read from JSON, and checked against the
four worked examples it appears in.

`fixtures/counter.cpn.json` is the same net as a file, and `scripts/check.sh` runs it through
the mCRL2 toolset. What that cannot do is check anything about the *semantics*: `mcrl22lps`
only ever sees the emitted text. This file closes that half. `Cpn2mCrl2/Semantics.lean` is
computable, so Definitions 6 and 7 can be evaluated on this net and compared with what
Examples 4 and 5 print, by `decide`.

It is the counterpart of `Proof/Examples/CounterNet.lean`, `CounterNetGraph.lean` and
`CounterNetLPE.lean`, and it checks the same three things those do -- with one addition those
cannot make, because their `LPE` is not syntax: the mCRL2 *text*.

## What is checked

* `net_valid` : the net passes the T1 validation of `Implementation/docs/InputFormat.md` §4.3.
* `enabled_*`, `fire_*` : Examples 4 and 5, evaluated.
* `not_enabled_t2_M₅` : the correction `Thesis/docs/ColoredPetriNets.md` records against
  Figure 3.4 -- in `M₅` the token in `p₂` carries 4, so `t2` is not enabled and the chain
  stops after seven states rather than eight.
* `expectedMcrl2`, `expectedMcrl2List` : the emitted text of both backends,
  character for character.
-/

namespace Cpn2mCrl2.Examples.Counter

/-! ## The net -/

/-- The variable `h`, the only one the net has. -/
def varH : Expr (.color .int) := .var "h" (.color .int)

/-- `{1`e}`, the shape every arc expression of this net has. -/
def tok (e : Expr (.color .int)) : Expr (.bag .int) := .single 1 e

/-- **Example 3.** The counter net: `p₁` starts with a token carrying 1; `t1` moves it to `p₂`
incremented by one; while the value is at most three `t2` moves it back to `p₁` unchanged;
once it is greater than three `t3` moves it to `p₃` unchanged. -/
def net : Net where
  colors := [.int, .bool]
  vars := [("h", .color .int)]
  places :=
    [ { name := "p1", color := .int, init := tok (.intLit 1) },
      { name := "p2", color := .int, init := .emptyBag .int },
      { name := "p3", color := .int, init := .emptyBag .int } ]
  transitions :=
    [ { name := "t1", guard := .boolLit true },
      { name := "t2", guard := .le varH (.intLit 3) },
      { name := "t3", guard := .lt (.intLit 3) varH } ]
  inArcs :=
    [ { place := "p1", transition := "t1", color := .int, expr := tok varH },
      { place := "p2", transition := "t2", color := .int, expr := tok varH },
      { place := "p2", transition := "t3", color := .int, expr := tok varH } ]
  outArcs :=
    [ { transition := "t1", place := "p2", color := .int, expr := tok (.add varH (.intLit 1)) },
      { transition := "t2", place := "p1", color := .int, expr := tok varH },
      { transition := "t3", place := "p3", color := .int, expr := tok varH } ]

/-- The net satisfies every T1 check of `Implementation/docs/InputFormat.md` §4.3, which is
what the theorems of `Cpn2mCrl2/Correct.lean` run on. -/
theorem net_valid : net.Valid := by decide

/-- `t1`, `t2` and `t3`. -/
def t1 : TransDecl := { name := "t1", guard := .boolLit true }
def t2 : TransDecl := { name := "t2", guard := .le varH (.intLit 3) }
def t3 : TransDecl := { name := "t3", guard := .lt (.intLit 3) varH }

theorem t1_mem : t1 ∈ net.transitions := .head _
theorem t2_mem : t2 ∈ net.transitions := .tail _ (.head _)
theorem t3_mem : t3 ∈ net.transitions := .tail _ (.tail _ (.head _))

/-- The binding `⟨h = n⟩`. -/
def bind (n : Int) : Env
  | .color .int, _ => .int n
  | .color c, _ => c.junk
  | .bag _, _ => ∅
  | .list _, _ => []

/-! ## Examples 4 and 5: the seven-state chain

`M₀ ↠ M₁ ↠ … ↠ M₆`, each step with the binding that makes it occur. Definition 7 is a
function here, so each marking is the previous one fired. -/

/-- `M₀`, the initial marking: one token carrying 1 in `p₁`. -/
def M₀ : Marking := net.initialMarking

/-- `M₁`, after `t1⟨h = 1⟩`. -/
def M₁ : Marking := net.fire M₀ t1 (bind 1)
/-- `M₂`, after `t2⟨h = 2⟩`. -/
def M₂ : Marking := net.fire M₁ t2 (bind 2)
/-- `M₃`, after `t1⟨h = 2⟩`. -/
def M₃ : Marking := net.fire M₂ t1 (bind 2)
/-- `M₄`, after `t2⟨h = 3⟩`. -/
def M₄ : Marking := net.fire M₃ t2 (bind 3)
/-- `M₅`, after `t1⟨h = 3⟩`. -/
def M₅ : Marking := net.fire M₄ t1 (bind 3)
/-- `M₆`, after `t3⟨h = 4⟩`. -/
def M₆ : Marking := net.fire M₅ t3 (bind 4)

/-- **Example 4.** `(t1, ⟨h = 1⟩)` is enabled in `M₀`. -/
theorem enabled_M₀ : net.Enabled M₀ t1 (bind 1) := by decide

theorem enabled_M₁ : net.Enabled M₁ t2 (bind 2) := by decide
theorem enabled_M₂ : net.Enabled M₂ t1 (bind 2) := by decide
theorem enabled_M₃ : net.Enabled M₃ t2 (bind 3) := by decide
theorem enabled_M₄ : net.Enabled M₄ t1 (bind 3) := by decide
theorem enabled_M₅ : net.Enabled M₅ t3 (bind 4) := by decide

/-- The token values along the chain: `p₂` holds 2, then 3, then 4. -/
theorem M₁_p2 : (M₁ "p2").coeff (.int 2) = 1 := by decide
theorem M₃_p2 : (M₃ "p2").coeff (.int 3) = 1 := by decide
theorem M₅_p2 : (M₅ "p2").coeff (.int 4) = 1 := by decide

/-- And `p₁` is empty once the token has moved on. -/
theorem M₁_p1 : (M₁ "p1").coeff (.int 1) = 0 := by decide

/-- `M₆` has the token in `p₃`, which is where the chain ends. -/
theorem M₆_p3 : (M₆ "p3").coeff (.int 4) = 1 := by decide

/-- The only token `p₂` holds in `M₅` carries 4. -/
theorem M₅_p2_eq (v : Value) (hc : 0 < (M₅ "p2").coeff v) : v = .int 4 := by
  have he : (M₅ "p2").entries = [(.int 2, 0), (.int 3, 0), (.int 4, 1)] := by decide
  rw [Bag.coeff, he] at hc
  simp only [Bag.entryCoeff] at hc
  by_cases h4 : Value.int 4 = v
  · exact h4.symm
  · simp [h4] at hc

/-- **The correction to Figure 3.4.** In `M₅` the token in `p₂` carries 4, so *no* binding of
`t2` is enabled, and the eighth state Figure 3.4 draws cannot be reached.

`Thesis/docs/ColoredPetriNets.md` records this against Example 5, and
`Proof/Examples/CounterNetGraph.lean` proves it for the abstract net. This is the same
statement for the concrete one, quantified over every binding rather than over an enumerated
few: the arc expression forces the bound value to be the one token `p₂` holds, and the guard
then fails on it. -/
theorem not_enabled_t2_M₅ (b : Env) : ¬ net.Enabled M₅ t2 b := by
  rintro ⟨hpre, hguard⟩
  have h1 := (hpre _ (.head _)) (b (.color .int) "h")
  simp only [tok, varH, Expr.eval, Bag.coeff_single, ite_true] at h1
  have hval := M₅_p2_eq _ (Nat.lt_of_lt_of_le Nat.zero_lt_one h1)
  rw [Expr.Holds] at hguard
  simp only [t2, varH, Expr.eval, Value.asBool] at hguard
  simp only [hval] at hguard
  simp [Value.asInt] at hguard

/-! ## Example 9: the translation

The condition of each summand, as `Implementation/docs/Target.md` §2 prints it by hand -- and
in particular the third, which is where `Thesis/docs/mCRL2.md` records a deviation: the
translation yields the inclusion in the parameter of `p2`, not of `p3` as the thesis prints.

These are `#guard`s rather than theorems. A string equality is checked by evaluation, and
proving one with `native_decide` would put `Lean.ofReduceBool` in the axiom list of a
development that otherwise has none. -/

#guard Mcrl2.printExpr (net.condTerm t1) == "(({h: 1} <= p1) && true)"

#guard Mcrl2.printExpr (net.condTerm t2) == "(({h: 1} <= p2) && (h <= 3))"

-- The Example 9 correction, as text: t3 tests p2, not p3.
#guard Mcrl2.printExpr (net.condTerm t3) == "(({h: 1} <= p2) && (3 < h))"

/-- The whole specification, as `Implementation/docs/Target.md` §2 writes it out by hand for
Example 9 -- up to the union with and difference from the empty bag that Definition 14 puts at
every place a transition does not touch, and that the hand-written version silently drops. -/
def expectedMcrl2 : String := String.intercalate "\n"
  [ "act t1, t2, t3;",
    "",
    "proc Spec(p1 : Bag(Int), p2 : Bag(Int), p3 : Bag(Int)) =",
    "    sum h : Int . (({h: 1} <= p1) && true) -> t1 . Spec(((p1 - {h: 1}) + {:}), ((p2 - {:}) + {(h + 1): 1}), ((p3 - {:}) + {:}))",
    "  + sum h : Int . (({h: 1} <= p2) && (h <= 3)) -> t2 . Spec(((p1 - {:}) + {h: 1}), ((p2 - {h: 1}) + {:}), ((p3 - {:}) + {:}))",
    "  + sum h : Int . (({h: 1} <= p2) && (3 < h)) -> t3 . Spec(((p1 - {:}) + {:}), ((p2 - {h: 1}) + {:}), ((p3 - {:}) + {h: 1}));",
    "",
    "init Spec({1: 1}, {:}, {:});",
    "" ]

#guard net.toMcrl2 == expectedMcrl2


/-! ## The second backend

The same net through the list encoding of `Cpn2mCrl2/ListEncoding.lean`. Its LTS has the same
seven states here -- the counter never puts two tokens in a place, so no order is ever
ambiguous. `fixtures/multitoken.cpn.json` is the fixture where the two differ. -/

/-- The list-encoded specification, as `cpn2mcrl2 --list` prints it. -/
def expectedMcrl2List : String := String.intercalate "
"
  [ "map rm_Int : Int # List(Int) -> List(Int);",
    "    diff_Int : List(Int) # List(Int) -> List(Int);",
    "    sub_Int : List(Int) # List(Int) -> Bool;",
    "var _x, _y : Int;",
    "    _l, _m : List(Int);",
    "eqn rm_Int(_x, []) = [];",
    "    rm_Int(_x, _y |> _l) = if(_x == _y, _l, _y |> rm_Int(_x, _l));",
    "    diff_Int(_l, []) = _l;",
    "    diff_Int(_l, _y |> _m) = diff_Int(rm_Int(_y, _l), _m);",
    "    sub_Int([], _m) = true;",
    "    sub_Int(_y |> _l, _m) = (_y in _m) && sub_Int(_l, rm_Int(_y, _m));",
    "",
    "act t1, t2, t3;",
    "",
    "proc Spec(p1 : List(Int), p2 : List(Int), p3 : List(Int)) =",
    "    sum h : Int . (sub_Int([h], p1) && true) -> t1 . Spec(diff_Int(p1, [h]), (p2 ++ [(h + 1)]), p3)",
    "  + sum h : Int . (sub_Int([h], p2) && (h <= 3)) -> t2 . Spec((p1 ++ [h]), diff_Int(p2, [h]), p3)",
    "  + sum h : Int . (sub_Int([h], p2) && (3 < h)) -> t3 . Spec(p1, diff_Int(p2, [h]), (p3 ++ [h]));",
    "",
    "init Spec([1], [], []);",
    "" ]

#guard net.toMcrl2List == expectedMcrl2List

/-! ## T2 on this net

`Cpn2mCrl2/Correct.lean` proves the two identities for every valid net. Instantiated here they
say, of this net: the condition the translation prints for t2 holds in a marking under a
binding exactly when that binding element is enabled by Definition 6, and the term it prints
for p2 evaluates to the bag Definition 7 leaves there. -/

example (M : Marking) (b : Env) :
    Expr.Holds (net.condTerm t2) (M.toEnv b) ↔ net.Enabled M t2 b :=
  net.toLpe_cond net_valid t2 t2_mem M b

example (M : Marking) (b : Env) :
    Expr.eval (net.nextTerm t2 { name := "p2", color := .int, init := .emptyBag .int })
        (M.toEnv b)
      = net.fire M t2 b "p2" :=
  net.toLpe_next net_valid t2 (.tail _ (.head _)) M b

end Cpn2mCrl2.Examples.Counter
