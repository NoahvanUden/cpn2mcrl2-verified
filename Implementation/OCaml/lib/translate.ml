(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** Definition 14, the translation.

    Definition 14 writes

    {v
    c_t(d, h_t) = (forall p in pre(t) : E(p,t) subseteq s_p) and G(t)
    g_t(d, h_t) = ((s_p1 \ E(p1,t)) union E(t,p1), ..., (s_pn \ E(pn,t)) union E(t,pn))
    v}

    and this builds both, as terms of [Expr], from that text. The bounded quantifier is
    unfolded here rather than left to the data language, which is obligation 3 of
    [Implementation/docs/Plan.md] §4; [Expr.and_all] is the fold. *)

open Expr
open Net
open Lpe

(** One conjunct of [c_t]: [E(p,t) subseteq s_p], with [s_p] the place parameter. *)
let cond_conjunct a = EBagSubset (a.aexpr, EVar (a.aplace, BT a.acolor))

(** [c_t]: the inclusions over [pre(t)], and then the guard. *)
let cond_term n t =
  and_all (List.map cond_conjunct (pre n t.tname) @ [ t.guard ])

(** [E(p,t)] as a term of the place's own bag sort.

    [Net.expr_at] reads the arc expression at the place's color; the two agree for a valid net
    and the empty bag stands in otherwise. Where there is no arc at all, the empty bag is what
    Definition 7's convention on non-existing arcs prescribes anyway. *)
let consume_term n t d =
  match in_arc n d.pname t.tname with
  | Some a -> expr_at a d.pcolor
  | None -> EEmptyBag d.pcolor

(** [E(t,p)] as a term of the place's own bag sort, read as [consume_term] is. *)
let produce_term n t d =
  match out_arc n t.tname d.pname with
  | Some a -> expr_at a d.pcolor
  | None -> EEmptyBag d.pcolor

(** [g_t] at the place [d]: [(s_p \ E(p,t)) union E(t,p)]. *)
let next_term n t d =
  EBagUnion
    ( EBagDiff (EVar (d.pname, BT d.pcolor), consume_term n t d),
      produce_term n t d )

let next_entries n t ps =
  List.map
    (fun d -> (d.pname, { btcolor = d.pcolor; btterm = next_term n t d }))
    ps

(** The summand of [t]. [H_t] is [Var(t)], and [a_t] is [t] itself carrying no parameters, as
    the note under Definition 14 records. *)
let summand_of n t =
  {
    binder = var_of n t;
    cond = cond_term n t;
    act = t.tname;
    next = next_entries n t n.places;
  }

let place_params ps = List.map (fun d -> (d.pname, d.pcolor)) ps

let init_entries ps =
  List.map (fun d -> (d.pname, { btcolor = d.pcolor; btterm = d.pinit })) ps

(** {b Definition 14 (Translation).}

    One summand per transition, one bag-sorted parameter per place, and
    [d_0 = (I(p1)<>, ..., I(pn)<>)] — emitted as the closed initialization {i terms}, which
    denote those values without the translator ever evaluating anything. *)
let to_lpe n =
  {
    sorts = n.colors;
    params = place_params n.places;
    acts = trans_names n;
    summands = List.map (summand_of n) n.transitions;
    init = init_entries n.places;
  }
