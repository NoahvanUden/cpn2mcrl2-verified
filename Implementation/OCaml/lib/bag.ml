(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** Bags, finitely supported.

    Definition 1 models a bag over [S] as a total function [S -> N]. All three translators
    depart from that and represent one by its finite support, because
    [Implementation/docs/Plan.md] §4.1 requires it: inclusion between total functions is a
    quantifier over the whole color set and is not decidable, so [c_t] could not be a
    [Bool]-valued term. [Proof/] keeps the total function and pays for it by leaving the
    condition a proposition.

    An entry list may mention a value more than once — [union] is append — so [coeff] sums the
    matching entries rather than looking one up. [keys] is what turns that back into a set.

    The coefficients are [int] and not a natural-number type, which OCaml does not have.
    [src/Bag.dfy] gets non-negativity from Dafny's [nat] subset type; here it is an invariant
    to be stated and carried. [sub] is truncated subtraction in both, because Dafny's [nat]
    subtraction is integer subtraction anyway. *)

open Color

(** A bag, as its finite support. *)
type t = (value * int) list

(** Truncated subtraction, which is what [-] is on [N]. *)
let sub a b = if a >= b then a - b else 0

(** The coefficient of [v]: the sum of every entry that mentions it. *)
let rec coeff m v =
  match m with
  | [] -> 0
  | (v', n) :: rest -> (if value_eq v' v then n else 0) + coeff rest v

(** The empty bag. *)
let empty : t = []

(** The bag in which [v] has coefficient [n] and everything else has zero. *)
let single n v : t = [ (v, n) ]

(** Addition, which on the support is concatenation. *)
let union (m1 : t) (m2 : t) : t = m1 @ m2

(** The values [m] mentions, without repetition. *)
let keys (m : t) = Util.dedup (List.map fst m)

(** Truncated subtraction, one entry per distinct value of [m1]. *)
let diff (m1 : t) (m2 : t) : t =
  List.map (fun k -> (k, sub (coeff m1 k) (coeff m2 k))) (keys m1)

(** Inclusion, as a decision procedure.

    Only the values [m1] mentions need checking: every other value has coefficient zero in
    [m1], and zero is below anything. *)
let subset (m1 : t) (m2 : t) =
  Util.all (fun k -> coeff m1 k <= coeff m2 k) (keys m1)

(** Structural equality on bags, entry by entry. Needed because [Expr.eval] of an equality
    test compares denotations, and a denotation may be a bag. *)
let rec bag_eq (m1 : t) (m2 : t) : bool =
  match (m1, m2) with
  | [], [] -> true
  | (v1, n1) :: r1, (v2, n2) :: r2 -> value_eq v1 v2 && n1 = n2 && bag_eq r1 r2
  | _ -> false

(** Every value the bag mentions has the color [c]. *)
let of_color (m : t) c = Util.all (fun p -> value_of_color (fst p) c) m
