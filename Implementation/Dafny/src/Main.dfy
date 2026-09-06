/*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 */

/**
 * # `cpn2mcrl2`
 *
 * The command line around the verified core.
 *
 *     cpn2mcrl2 [--list] <net.cpn.json> [out.mcrl2]
 *
 * Reads the native CPN format of `Implementation/docs/InputFormat.md` 4, validates it (T1),
 * translates it (Definition 14), prints it (the encoding of
 * `Implementation/docs/Target.md` 1), and writes the result to a file or to standard output.
 *
 * With `--list` it prints the second backend of `Implementation/docs/Plan.md` 5 instead: a
 * `List` per place rather than a `Bag`, which `Thesis/docs/mCRL2.md` 4.1 measures at a
 * sevenfold speedup. `src/ListEncoding.dfy` proves the two denote bisimilar systems, so the
 * flag changes the speed and not the meaning.
 *
 * What a run establishes is exactly `Implementation/docs/Plan.md` 2's T1 and T2: the input is a
 * CPN, and the term printed denotes the `c_t` and `g_t` of Definition 14. Whether `mcrl22lps`
 * accepts the text is T0, which only running the tool can say; `scripts/check.sh` does that.
 */
module Cpn2Mcrl2Main {

  import opened Std.Wrappers
  import Std.FileIO
  import opened Std.BoundedInts
  import opened Util
  import opened Colors
  import opened Bags
  import opened ListOps
  import opened Exprs
  import opened Nets
  import opened Semantics
  import opened Lpes
  import opened Translate
  import opened Correct
  import opened ListEncoding
  import opened Print
  import opened PrintList
  import opened Import

  const Usage: string :=
    "usage: cpn2mcrl2 [--list] <net.cpn.json> [out.mcrl2]\n\n"
    + "Translates a Colored Petri Net in the native JSON format into an mCRL2\n"
    + "specification. With no output file the specification goes to stdout.\n\n"
    + "--list  emit the list-encoded backend, one List per place instead of one\n"
    + "        Bag per place. The two denote bisimilar systems; the list one is faster."

  /** Everything the printer can emit is ASCII: `IsSafeIdent` admits only ASCII identifiers,
    * and the rest of the output is punctuation and decimal digits. A character outside that
    * range would be a printer bug, and `?` in the output is a louder symptom than a crash. */
  function BytesOfString(s: string): seq<bv8>
  {
    if |s| == 0 then []
    else
      var c := s[0] as int;
      [(if 0 <= c < 128 then c else 63) as bv8] + BytesOfString(s[1..])
  }

  /** Dafny 4.11 does not allow `Main` a non-ghost out parameter, so there is no exit code to
    * set: a refused net is reported on standard output and no specification is produced.
    * `scripts/check.sh` therefore runs every fixture with an output path and reads "the file
    * was not written" as the rejection, which is what the Lean translator says with a non-zero
    * exit. */
  method Main(args: seq<string>) {
    var rest: seq<string> := [];
    var useList := false;
    var i := 1;
    while i < |args|
      invariant 1 <= i
      decreases |args| - i
    {
      if args[i] == "--list" {
        useList := true;
      } else {
        rest := rest + [args[i]];
      }
      i := i + 1;
    }

    if |rest| == 0 {
      print Usage, "\n";
      return;
    }

    var input := rest[0];
    var readResult := FileIO.ReadBytesFromFile(input);
    if readResult.Failure? {
      print input, ": cannot be read\n";
      return;
    }

    var netResult := NetOfBytes(readResult.value);
    match netResult {
      case Failure(msg) =>
        print input, ": ", msg, "\n";

      case Success(n) =>
        var out := if useList then ToMcrl2List(n) else ToMcrl2(n);

        if |rest| == 1 {
          print out;
        } else {
          var w := FileIO.WriteBytesToFile(rest[1], BytesOfString(out));
          if w.Failure? {
            print rest[1], ": cannot be written\n";

          }
        }
    }
  }
}
