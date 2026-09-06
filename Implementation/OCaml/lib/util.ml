(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** List utilities, written inside the fragment of OCaml that Cameleer reads.

    This module had an earlier life. Written idiomatically it was 25 lines, against
    [Cpn2mCrl2/Util.lean]'s 50 and [src/Util.dfy]'s 247, because [List.for_all],
    [List.concat_map], [List.find_opt] and [String.concat] all carry the meanings this
    translator needs. Cameleer knows none of them, so they are written out here — which puts
    the file back where the other two are, and for a third distinct reason. Lean writes them
    out to keep Mathlib outside the trust boundary; Dafny writes them out because a proof has
    to unfold the definition it is about; here they are written out because the verifier has
    never heard of them.

    [List.mem], [List.map], [List.filter] and [@] {i are} known, so those stay.

    {2 Equality}

    Cameleer types [=] as [int -> int -> bool] in program code. Not strings, not booleans, not
    user datatypes. So every type this translator compares needs a decidable equality written
    by hand — the thing Lean derives with [deriving DecidableEq] and Dafny gives away with
    [(==)] on any datatype. [String.equal] is the one exception the standard library supplies.

    [dedup] keeps the {i last} occurrence of each element. Nothing here depends on that; it
    matches the other two translators so that all three emit the summation variables of a
    summand in the same order and their outputs can be compared as text. *)

(** Equality on strings. The standard library's, which Cameleer does know. *)
let string_eq (a : string) (b : string) : bool = String.equal a b

(** Every element of [l] satisfies [p]. [List.for_all] by hand. *)
let rec all (p : 'a -> bool) (l : 'a list) : bool =
  match l with [] -> true | x :: rest -> p x && all p rest

(** The first element of [l] satisfying [p], if any. [List.find_opt] by hand. *)
let rec find (p : 'a -> bool) (l : 'a list) : 'a option =
  match l with
  | [] -> None
  | x :: rest -> if p x then Some x else find p rest

(** [f] applied to each element, concatenated. [List.concat_map] by hand. *)
let rec flat_map (f : 'a -> 'b list) (l : 'a list) : 'b list =
  match l with [] -> [] | x :: rest -> f x @ flat_map f rest

(** No element of [l] occurs twice.

    Recursive rather than quantified, so that a proof about [x :: l] can unfold one step. *)
let rec no_dup (l : 'a list) : bool =
  match l with [] -> true | x :: rest -> (not (List.mem x rest)) && no_dup rest

(** [a] prepended to [l], unless [l] already contains it. *)
let insert_new (a : 'a) (l : 'a list) : 'a list =
  if List.mem a l then l else a :: l

(** [l] without repetitions, keeping the last occurrence of each element. *)
let rec dedup (l : 'a list) : 'a list =
  match l with [] -> [] | x :: rest -> insert_new x (dedup rest)

(** The value the key [k] is associated with, if any. The first entry wins. *)
let rec lookup (l : (string * 'a) list) (k : string) : 'a option =
  match l with
  | [] -> None
  | (k', v) :: rest -> if string_eq k' k then Some v else lookup rest k

(** [l] with the entries whose keys repeat an earlier one dropped, keeping the first.

    Used to emit one sort declaration per color rather than one per mention. *)
let dedup_by (key : 'a -> string) (l : 'a list) : 'a list =
  let rec go seen l =
    match l with
    | [] -> []
    | x :: rest ->
        if List.mem (key x) seen then go seen rest
        else x :: go (key x :: seen) rest
  in
  go [] l
