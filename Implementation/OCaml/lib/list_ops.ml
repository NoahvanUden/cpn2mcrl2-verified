(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** Lists as bags.

    The second backend of [Implementation/docs/Plan.md] §5 stores one [List] per place instead
    of one [Bag], because [Thesis/docs/mCRL2.md] §4.1 measures that as seven times faster.
    A list is a {i representative} of a bag, and this module is the correspondence: the
    multiset operations on lists, stated against Definition 1's operations on the bag the list
    represents.

    [count_of], [erase_first], [list_diff] and [sub_multiset] are written out recursively
    rather than assembled from [List.filter] and friends, and here that is not a stylistic
    choice. Every proof in [List_encoding] is an induction on one of them, so the definition a
    proof unfolds has to be the definition. Where the standard library does carry the meaning
    this translator needs — as it does throughout [Util] — it is used instead. *)

open Color

(** Whether [l] holds [v]. *)
let rec mem_value (v : value) (l : value list) : bool =
  match l with [] -> false | x :: rest -> value_eq x v || mem_value v rest

(** How many times [l] holds [v]. *)
let rec count_of l v =
  match l with [] -> 0 | x :: rest -> (if value_eq x v then 1 else 0) + count_of rest v

(** The bag a list represents: every element with multiplicity one, so the coefficient of a
    value is the number of times the list holds it. *)
let bag_of_list (l : value list) : Bag.t = List.map (fun v -> (v, 1)) l

(** [l] without its first occurrence of [v], or [l] unchanged if it holds none. *)
let rec erase_first l v =
  match l with
  | [] -> []
  | x :: rest -> if value_eq x v then rest else x :: erase_first rest v

(** [a] with one occurrence of each element of [b] removed. Definition 1's operation 6. *)
let rec list_diff a b =
  match b with [] -> a | x :: rest -> list_diff (erase_first a x) rest

(** Multiset inclusion, as a decision procedure. Definition 1's operation 5.

    Written as "remove [a]'s elements from [b] one at a time and never run out" rather than as
    a comparison of counts. The two agree — that is the lemma [List_encoding] needs — and this
    form is the one that recurses structurally on [a]. *)
let rec sub_multiset a b =
  match a with
  | [] -> true
  | x :: rest -> mem_value x b && sub_multiset rest (erase_first b x)
