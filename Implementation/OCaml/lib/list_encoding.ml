(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** The second backend: one [List] per place instead of one [Bag].

    [Thesis/docs/mCRL2.md] §4.1 measures the bag encoding at 67 seconds on the thesis's own
    benchmark and the list encoding at 9, which is why the reference generator emits lists.
    Definition 14 stores bags, so the fast output is a {i refinement} of the object Theorem 1 is
    about, and [Implementation/docs/Plan.md] §5 calls proving it "the largest unacknowledged gap
    in the project".

    This file is the translation. The refinement itself — that a list marking is a faithful
    representative of the bag marking it stands for, and that the production order does not
    matter — is the part that needs proof, and is not here yet.

    Of the two refinements §5 separates, {i typing} is discharged by construction: this backend
    emits [List(C(p))], one list sort per place at that place's own color, rather than the
    reference generator's shared tagged union, so there is no invariant to preserve. {i Order}
    is the lemma. *)

open Color
open Expr
open Net

(** [k] copies of [e], as a list term built from [[]] by [<|]. *)
let rec replicate_t c k e =
  if k <= 0 then ENilList c else ESnoc (replicate_t c (k - 1) e, e)

(** A bag term as the list term denoting one of its representatives.

    The color is an argument and there is a fallback branch, because the sort of a term is
    inferred here rather than carried in its type. [Cpn2mCrl2/ListEncoding.lean] takes neither:
    its [Expr] is indexed, so the color comes from the index — at the price of five equation
    lemmas beside it, because Lean's matcher discriminates on that index and so does not reduce
    definitionally. The fallback is unreachable for any term this backend builds. *)
let rec bag_to_list c e =
  match e with
  | EVar (x, BT c0) -> EVar (x, LT c0)
  | EVar (_, _) -> ENilList c
  | EEmptyBag c0 -> ENilList c0
  | ESingle (k, e0) -> replicate_t c k e0
  | EBagUnion (a, b) -> EAppendList (bag_to_list c a, bag_to_list c b)
  | EBagDiff (a, b) -> EDiffList (bag_to_list c a, bag_to_list c b)
  | _ -> ENilList c

(** A list-sorted term together with the color of its elements. *)
type list_term = { ltcolor : color; ltterm : expr }

(** One summand of the list-encoded LPE. *)
type list_summand = {
  lbinder : ctx;
  lcond : expr;
  lact : string;
  lnext : (string * list_term) list;
}

(** Definition 13 with a list per place instead of a bag. *)
type list_lpe = {
  lsorts : color list;
  lparams : (string * color) list;
  lacts : string list;
  lsummands : list_summand list;
  linit : (string * list_term) list;
}

(** One conjunct of the list condition: [E(p,t) <= s_p] as multiset inclusion on lists. *)
let list_cond_conjunct a =
  ESubList (bag_to_list a.acolor a.aexpr, EVar (a.aplace, LT a.acolor))

let list_cond_term n t =
  and_all (List.map list_cond_conjunct (pre n t.tname) @ [ t.guard ])

(** The list at [p] after [t] has taken its tokens out.

    Where there is no arc the list is left alone rather than differenced against the empty list,
    which is what keeps the emitted text free of the [\ 0] the bag encoding writes. *)
let list_consumed n t d =
  match in_arc n d.pname t.tname with
  | Some a ->
      EDiffList
        (EVar (d.pname, LT d.pcolor), bag_to_list d.pcolor (expr_at a d.pcolor))
  | None -> EVar (d.pname, LT d.pcolor)

(** [g_t] at the place [d], in the list encoding. *)
let list_next_term n t d =
  match out_arc n t.tname d.pname with
  | Some a ->
      EAppendList (list_consumed n t d, bag_to_list d.pcolor (expr_at a d.pcolor))
  | None -> list_consumed n t d

let list_next_entries n t ps =
  List.map
    (fun d -> (d.pname, { ltcolor = d.pcolor; ltterm = list_next_term n t d }))
    ps

let list_summand_of n t =
  {
    lbinder = var_of n t;
    lcond = list_cond_term n t;
    lact = t.tname;
    lnext = list_next_entries n t n.places;
  }

let list_init_entries ps =
  List.map
    (fun d -> (d.pname, { ltcolor = d.pcolor; ltterm = bag_to_list d.pcolor d.pinit }))
    ps

(** {b The list-encoded LPE}: [Implementation/docs/Plan.md] §5's second backend, behind the same
    translation as the first. *)
let to_lpe_list n =
  {
    lsorts = n.colors;
    lparams = Translate.place_params n.places;
    lacts = trans_names n;
    lsummands = List.map (list_summand_of n) n.transitions;
    linit = list_init_entries n.places;
  }
