(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** List utilities.

    The counterparts of this module in the other two translators are the largest of their
    support files: [Cpn2mCrl2/Util.lean] is 50 lines and [src/Util.dfy] is 247, because both
    write out [map], [filter], [flat_map], [for_all], [concat] and integer printing by hand.
    Neither does that for want of a library. Lean's reason is to keep Mathlib outside the
    trust boundary; Dafny's is that a proof has to unfold the definition it is about, and a
    recursive [NoDup] and a quantified one are interchangeable as specifications but not as
    proof obligations.

    Here [List.map], [List.filter], [List.concat_map], [List.for_all], [List.find_opt],
    [String.concat], [String.compare] and [string_of_int] are all in the standard library
    with the meanings this translator needs, so what is left is only what is genuinely
    specific: duplicate removal that keeps the *last* occurrence, association lookup, and
    sorting an association list by its key.

    [dedup] keeping the last occurrence is not an accident and nothing here depends on it.
    It matches [Cpn2mCrl2/Util.lean] so that all three translators emit the summation
    variables of a summand in the same order and their outputs can be compared as text. *)

(** No element of [l] occurs twice.

    Recursive rather than quantified, so that a proof about [x :: l] can unfold one step. *)
let rec no_dup = function
  | [] -> true
  | x :: rest -> (not (List.mem x rest)) && no_dup rest

(** [a] prepended to [l], unless [l] already contains it. *)
let insert_new a l = if List.mem a l then l else a :: l

(** [l] without repetitions, keeping the last occurrence of each element. *)
let rec dedup = function [] -> [] | x :: rest -> insert_new x (dedup rest)

(** The value [k] is associated with, if any. The first entry wins. *)
let rec lookup l k =
  match l with
  | [] -> None
  | (k', v) :: rest -> if k' = k then Some v else lookup rest k

(** [l] with the entries whose keys repeat an earlier one dropped, keeping the first.

    Used to emit one sort declaration per color rather than one per mention. *)
let dedup_by key l =
  let rec go seen = function
    | [] -> []
    | x :: rest ->
        if List.mem (key x) seen then go seen rest
        else x :: go (key x :: seen) rest
  in
  go [] l

(** An association list sorted by its key, so that the importer can present the members of a
    JSON object in a canonical order.

    [List.stable_sort] rather than a hand-written insertion sort: a JSON object cannot have
    two members of the same name, so stability is not observable here, but it is what makes
    this agree with the insertion sort the other two translators use. *)
let sort_by_key l = List.stable_sort (fun (a, _) (b, _) -> String.compare a b) l
