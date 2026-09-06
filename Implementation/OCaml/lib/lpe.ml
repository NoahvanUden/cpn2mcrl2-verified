(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** Definition 13, as data.

    An LPE is

    {v Spec(d : D) = sum_{k in K} sum_{h_k : H_k} c_k(d, h_k) -> a_k . Spec(g_k(d, h_k)) v}

    and this is that, syntactically: [c_k] and [g_k] are {i terms} of [Expr], not functions.
    That is the shape [Proof/] acquired at milestone M2 and the shape both other translators
    have had from the start. *)

open Color
open Expr

(** A bag-sorted term together with the color of its elements. The color is carried because
    the printer needs it to write [{:}] at the right sort, and reconstructing it from the term
    would mean re-running [sort_of]. *)
type bag_term = { btcolor : color; btterm : expr }

(** One summand: [sum_{h_k : H_k} c_k(d, h_k) -> a_k . Spec(g_k(d, h_k))]. *)
type summand = {
  binder : ctx;  (** [H_k], as the variables the [sum] binds. *)
  cond : expr;  (** [c_k], a boolean term over the place parameters and the binder. *)
  act : string;  (** [a_k], a label carrying no parameters, as Definition 14 records. *)
  next : (string * bag_term) list;
      (** [g_k], one bag term per place, keyed by the place's name. A place the list does not
          mention keeps its marking. *)
}

(** An LPE: the sorts it declares, the process parameters, the action labels, the summands,
    and [d_0] as one closed term per place. *)
type t = {
  sorts : color list;
  params : (string * color) list;
  acts : string list;
  summands : summand list;
  init : (string * bag_term) list;
}
