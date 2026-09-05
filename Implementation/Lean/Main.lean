/-
Copyright (c) 2026 Noah van Uden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah van Uden
-/
import Cpn2mCrl2

/-!
# `cpn2mcrl2`

The command line around the verified core.

    cpn2mcrl2 [--list] <net.cpn.json> [out.mcrl2]

Reads the native CPN format of `Implementation/docs/InputFormat.md` §4, validates it (T1),
translates it (Definition 14), prints it (the encoding of
`Implementation/docs/Target.md` §1), and writes the result to a file or to standard output.

With `--list` it prints the second backend of `Implementation/docs/Plan.md` §5 instead: a
`List` per place rather than a `Bag`, which `Thesis/docs/mCRL2.md` §4.1 measures at a
sevenfold speedup. `Cpn2mCrl2/ListEncoding.lean` proves the two denote bisimilar systems, so
the flag changes the speed and not the meaning.

What a run establishes is exactly `Implementation/docs/Plan.md` §2's T1 and T2: the input is a
CPN, and the term printed denotes the `c_t` and `g_t` of Definition 14. Whether `mcrl22lps`
accepts the text is T0, which only running the tool can say; `scripts/check.sh` does that.
-/

open Cpn2mCrl2

def usage : String :=
  "usage: cpn2mcrl2 [--list] <net.cpn.json> [out.mcrl2]\n\n\
   Translates a Colored Petri Net in the native JSON format into an mCRL2\n\
   specification. With no output file the specification goes to stdout.\n\n\
   --list  emit the list-encoded backend, one List per place instead of one\n\
   Bag per place. The two denote bisimilar systems; the list one is faster."

def main (args : List String) : IO UInt32 := do
  let useList := args.contains "--list"
  match args.filter (· != "--list") with
  | [] =>
    IO.eprintln usage
    return 1
  | input :: rest =>
    let text ← IO.FS.readFile input
    match Net.ofJsonString text with
    | .error e =>
      IO.eprintln s!"{input}: {e}"
      return 1
    | .ok ⟨net, _⟩ =>
      let out := if useList then net.toMcrl2List else net.toMcrl2
      match rest with
      | [] => IO.print out
      | target :: _ => IO.FS.writeFile target out
      return 0
