(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtMisc
open CoqTerms
open SmtTrace
open SmtAtom
open SmtBtype
open SmtCertif
open Lexing

(* let debug = false *)


(******************************************************************************)
(* Given a cvc5 alethe trace build the corresponding certif and theorem             *)
(******************************************************************************)
(* exception Import_trace of int *)

(* let get_val = function
 *     Some a -> a
 *   | None -> assert false *)

(* For debugging certif processing : <add_scertif> <select> <occur> <alloc> *)
(* let print_certif c where=
 *   let r = ref c in
 *   let out_channel = open_out where in
 *   let fmt = Format.formatter_of_out_channel out_channel in
 *   let continue = ref true in
 *   while !continue do
 *     let kind = to_string (!r.kind) in
 *     let id = !r.id in
 *     let pos = match !r.pos with
 *       | None -> "None"
 *       | Some p -> string_of_int p in
 *     let used = !r.used in
 *     Format.fprintf fmt "id:%i kind:%s pos:%s used:%i value:" id kind pos used;
 *     begin match !r.value with
 *     | None -> Format.fprintf fmt "None"
 *     | Some l -> List.iter (fun f -> Form.to_smt Atom.to_smt fmt f;
 *                                     Format.fprintf fmt " ") l end;
 *     Format.fprintf fmt "\n";
 *     match !r.next with
 *     | None -> continue := false
 *     | Some n -> r := n
 *   done;
 *   Format.fprintf fmt "@."; close_out out_channel *)

let print_position lexbuf = 
  let pos = lexbuf.lex_curr_p in
  "Line "^(string_of_int pos.pos_lnum)^" Position "^(string_of_int (pos.pos_cnum - pos.pos_bol + 1))
 
let import_trace ra_quant rf_quant filename first lsmt =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  try
    let cert = VeritParser.proof VeritLexer.token lexbuf in
    let cert' = VeritAst.preprocess_certif cert in
    try
      let cert_proc = VeritAst.process_certif cert' in
      let first_num = List.hd cert_proc in
      let confl_num = List.nth cert_proc ((List.length cert_proc) - 1) in
         close_in chan;
         let cfirstcl =
          try VeritSyntax.get_clause first_num with
            | VeritSyntax.Debug s -> raise (VeritSyntax.Debug 
                ("| Cvc5.import_trace: fetching first certif step |"^s)) in
         let conflcl =
          try VeritSyntax.get_clause confl_num with
            | VeritSyntax.Debug s -> raise (VeritSyntax.Debug
                ("| Cvc5.import_trace: fetching last certif step |"^s)) in
         let cfirst = ref cfirstcl in
         let confl = ref conflcl in
         let re_hash = Form.hash_hform (Atom.hash_hatom ra_quant) rf_quant in
         begin match first with
         | None -> ()
         | Some _ ->
            let init_index = VeritSyntax.init_index lsmt re_hash in
            let cf, lr = order_roots init_index !cfirst in
            cfirst := cf;
            let to_add = VeritSyntax.qf_to_add (List.tl lr) in
            let to_add =
              (match first, !cfirst.value with
               | Some (root, l), Some [fl] when init_index fl = 1 && not (Form.equal l (re_hash fl)) ->
                   let cfirst_value = !cfirst.value in
                   !cfirst.value <- root.value;
                   [Other (ImmFlatten (root, fl)), cfirst_value, !cfirst]
               | _ -> []) @ to_add in
         match to_add with
         | [] -> ()
         | _  -> confl := add_scertifs to_add !cfirst end;
         select !confl;
         occur !confl;
         (alloc !cfirst, !confl)
    with
    | VeritSyntax.Debug s -> CoqInterface.error ("Cvc5.import_trace (VeritSyntax.Debug)\nPosition: "^(print_position lexbuf)
        ^"\nMessage: "^s^"\nCertificate:\n"^(VeritAst.string_of_certif (cert'))^"\nHash Table:\n"^(VeritSyntax.clauses_to_string))
    | Failure f -> CoqInterface.error ("Cvc5.import_trace (Failure)\nPosition: "^(print_position lexbuf)^"\nMessage: "^f)
    | _ -> CoqInterface.error ("Cvc5.import_trace\nPosition: "^(print_position lexbuf))
  with
  | VeritParser.Error -> CoqInterface.error ("Cvc5.import_trace (VeritParser.Error)\nPosition: "^(print_position lexbuf))


let clear_all () =
  SmtTrace.clear ();
  SmtMaps.clear ();
  VeritAst.clear_sterms ();
  VeritSyntax.clear ()


let import_all fsmt fproof =
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra_quant = VeritSyntax.ra_quant in
  let rf_quant = VeritSyntax.rf_quant in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace ra_quant rf_quant fproof None [] in
  (rt, ro, ra, rf, roots, max_id, confl)


let parse_certif t_i t_func t_atom t_form root used_root trace fsmt fproof =
  SmtCommands.parse_certif t_i t_func t_atom t_form root used_root trace
    (import_all fsmt fproof)

let checker_debug fsmt fproof =
  SmtCommands.checker_debug (import_all fsmt fproof)

let theorem name fsmt fproof =
  SmtCommands.theorem name (import_all fsmt fproof)

let checker fsmt fproof =
  SmtCommands.checker (import_all fsmt fproof)



(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)

let export out_channel rt ro lsmt =
  let fmt = Format.formatter_of_out_channel out_channel in
  Format.fprintf fmt "(set-logic UFLIA)@.";

  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    SmtMaps.add_btype s (Tindex t);
    Format.fprintf fmt "(declare-sort %s 0)@." s
  ) (SmtBtype.to_list rt);

  List.iter (fun (i,dom,cod,op) ->
    let s = "op_"^(string_of_int i) in
    SmtMaps.add_fun s op;
    Format.fprintf fmt "(declare-fun %s (" s;
    let is_first = ref true in
    Array.iter (fun t -> if !is_first then is_first := false else Format.fprintf fmt " "; SmtBtype.to_smt fmt t) dom;
    Format.fprintf fmt ") ";
    SmtBtype.to_smt fmt cod;
    Format.fprintf fmt ")@."
  ) (Op.to_list ro);

  List.iter (fun u -> Format.fprintf fmt "(assert ";
                      Form.to_smt fmt u;
                      Format.fprintf fmt ")\n") lsmt;

  Format.fprintf fmt "(check-sat)\n(exit)@."

exception Unknown

let call_cvc5 _ rt ro ra_quant rf_quant first lsmt =
  let (filename, outchan) = Filename.open_temp_file "cvc5_coq" ".smt2" in
  export outchan rt ro lsmt;
  close_out outchan;
  let logfilename = Filename.chop_extension filename ^ ".vtlog" in
  let wname, woc = Filename.open_temp_file "warnings_cvc5" ".log" in
  close_out woc;
  let command = "cvc5 --dump-proofs --proof-prune-input --proof-format-mode=alethe --simplification=none --dag-thres=0 --lang=smt2 --proof-granularity=dsl-rewrite " ^ filename ^ " | tail -n +2 > " ^ logfilename ^ " 2> " ^ wname in
  Format.eprintf "%s@." command;
  let t0 = Sys.time () in
  let exit_code = Sys.command command in
  let t1 = Sys.time () in
  Format.eprintf "cvc5 = %.5f@." (t1-.t0);

  let win = open_in wname in

  let raise_warnings_errors () =
    try
      while true do
        let l = input_line win in
        let n = String.length l in
        if l = "warning : proof_done: status is still open" then
          raise Unknown
        else if l = "Invalid memory reference" then
          CoqInterface.warning "cvc5-warning" ("cvc5 outputted the warning: " ^ l)
        else if n >= 7 && String.sub l 0 7 = "warning" then
          CoqInterface.warning "cvc5-warning" ("cvc5 outputted the warning: " ^ (String.sub l 7 (n-7)))
        else if n >= 8 && String.sub l 0 8 = "error : " then
          CoqInterface.error ("cvc5 failed with the error: " ^ (String.sub l 8 (n-8)))
        else
          CoqInterface.error ("cvc5 failed with the error: " ^ l)
      done
    with End_of_file -> () in

  try
    if exit_code <> 0 then CoqInterface.warning "cvc5-non-zero-exit-code" ("Cvc5.call_cvc5: command " ^ command ^ " exited with code " ^ string_of_int exit_code);
    raise_warnings_errors ();
    let res = import_trace ra_quant rf_quant logfilename (Some first) lsmt in
    close_in win; Sys.remove wname; res
  with x -> close_in win; Sys.remove wname;
            match x with
            | Unknown -> CoqInterface.error "cvc5 returns 'unknown'"
            | VeritSyntax.Sat -> CoqInterface.error "cvc5 found a counter-example"
            | _ -> raise x

let cvc5_logic =
  SL.of_list [LUF; LLia]

let tactic_gen vm_cast lcpl lcepl =
  (* Transform the tuple of lemmas given by the user into a list *)
  let lcpl =
    let lcpl = EConstr.Unsafe.to_constr lcpl in
    let lcpl = CoqTerms.option_of_constr_option lcpl in
    match lcpl with
      | Some lcpl -> CoqTerms.list_of_constr_tuple lcpl
      | None -> []
  in

  (* Core tactic *)
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra_quant = VeritSyntax.ra_quant in
  let rf_quant = VeritSyntax.rf_quant in
  SmtCommands.tactic call_cvc5 cvc5_logic rt ro ra rf ra_quant rf_quant vm_cast lcpl lcepl
let tactic = tactic_gen vm_cast_true
let tactic_no_check = tactic_gen (fun _ -> vm_cast_true_no_check)
