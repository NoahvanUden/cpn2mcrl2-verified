(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** Definitions 6 to 9: the reference side of the T2 theorems.

    Nothing the translator does depends on this module. It exists so that "the emitted term
    denotes [c_t] and [g_t]" has a left-hand side, and Definitions 6 and 7 are what that
    left-hand side is.

    {2 Where the ghost boundary went}

    [src/Semantics.dfy] marks every one of these [ghost], so Dafny guarantees they are absent
    from the compiled artifact. [Cpn2mCrl2/Semantics.lean] uses ordinary definitions in a module
    the translator does not import. OCaml has neither device: what is here is live code that the
    translator never calls, and the only thing keeping it out of the binary is that nothing
    references it.

    The boundary does not disappear, though — it moves and becomes visible. [enabled] and
    [occurs] cannot be written as OCaml at all, because Definition 6 compares bags with
    Definition 1's inclusion, which quantifies over the whole color set and is not decidable.
    Those two are GOSPEL predicates, in the annotations rather than in the code. In Dafny the
    same split exists and is called [Subset] against [SubsetB]; here one half is a different
    language. *)

open Expr
open Net

(** A marking maps each place to the bag of tokens it holds. *)
type marking = string -> Bag.t

(** The environment in which Definition 14's terms are read: the place parameters [s_p] hold the
    marking, and the summation variables hold the transition's binding.

    This is where the two tuples of Definition 13 are realized. [d : D] is the marking, spread
    over one bag-sorted variable per place; [h_t : H_t] is the binding, spread over one
    color-sorted variable per element of [Var(t)]. *)
let to_env (m : marking) (b : env) : env =
 fun t x ->
  match t with CT _ -> b t x | BT _ -> DBag (m x) | LT _ -> DList []

(** The tokens [t] consumes from [p] under the binding [b]: the value of [E(p, t)], or the empty
    bag when there is no such arc — the convention of §2.1.1 on arc expressions of non-existing
    arcs. *)
let consume n t (b : env) p =
  match in_arc n p t with
  | Some a -> as_bag (eval a.aexpr b)
  | None -> Bag.empty

(** The tokens [t] produces in [p] under [b], read with the same convention. *)
let produce n t (b : env) p =
  match out_arc n t p with
  | Some a -> as_bag (eval a.aexpr b)
  | None -> Bag.empty

(** [M0(p) = I(p)<>]. The initialization expressions are closed — [Net.init_closed] — so the
    binding they are evaluated under does not matter. *)
let initial_marking n : marking =
 fun p ->
  match find_place n.places p with
  | Some d -> as_bag (eval d.pinit junk_env)
  | None -> Bag.empty

(** {b Definition 7 (Occurring binding element).}

    The marking reached when [(t, b)] occurs in [m]: every place loses the tokens [t] consumes
    from it and gains the tokens [t] produces in it. *)
let fire n (m : marking) t (b : env) : marking =
 fun p -> Bag.union (Bag.diff (m p) (consume n t.tname b p)) (produce n t.tname b p)
