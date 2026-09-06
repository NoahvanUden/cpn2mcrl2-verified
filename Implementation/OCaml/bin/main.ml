(*
 * Copyright (c) 2026 Noah van Uden. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Authors: Noah van Uden
 *)

(** The command line: a CPN file in, an mCRL2 specification out. *)

let usage =
  "usage: cpn2mcrl2 [--list] <input.cpn.json> [output.mcrl2]\n\n\
  \  --list   emit one List per place instead of one Bag\n\n\
   Without an output path the specification goes to standard output.\n"

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let list_mode = List.mem "--list" args in
  match List.filter (fun a -> a <> "--list") args with
  | [] | _ :: _ :: _ :: _ ->
      prerr_string usage;
      exit 2
  | input :: rest -> (
      match Cpn2mcrl2.Import.net_of_string (read_file input) with
      | Error msg ->
          prerr_endline ("cpn2mcrl2: " ^ msg);
          exit 1
      | Ok net ->
          let text =
            if list_mode then Cpn2mcrl2.Print_list.to_mcrl2_list net
            else Cpn2mcrl2.Print.to_mcrl2 net
          in
          (match rest with
          | [] -> print_string text
          | out :: _ ->
              let oc = open_out_bin out in
              output_string oc text;
              close_out oc))
