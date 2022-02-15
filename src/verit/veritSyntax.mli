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


open SmtAtom

exception Sat
exception Debug of string
type typ = 
  | Assume (* Inpu *)
  | True
  | Fals
  | Notnot (* New *)
  | Threso (* New *)
  | Reso
  | Taut (* New *)
  | Cont (* New *)
  | Refl (* New *)
  | Trans (* New *)
  | Cong (* New *)
  | Eqre
  | Eqtr
  | Eqco
  | Eqcp
  | And
  | Nor
  | Or
  | Nand
  | Xor1 
  | Xor2
  | Nxor1 
  | Nxor2
  | Imp
  | Nimp1
  | Nimp2
  | Equ1
  | Equ2
  | Nequ1
  | Nequ2
  | Andp
  | Andn
  | Orp
  | Orn
  | Xorp1
  | Xorp2
  | Xorn1
  | Xorn2
  | Impp
  | Impn1
  | Impn2
  | Equp1
  | Equp2
  | Equn1
  | Equn2
  | Ite1
  | Ite2
  | Itep1
  | Itep2
  | Iten1
  | Iten2
  | Nite1
  | Nite2
  | Conndef (* New *)
  | Andsimp (* New *)
  | Orsimp (* New *)
  | Notsimp (* New *)
  | Impsimp (* New *)
  | Eqsimp (* New *)
  | Boolsimp (* New *)
  | Acsimp (* New *)
  | Itesimp (* New *)
  | Equalsimp (* New *)
  | Distelim (* New *)
  | Lage
  | Liage
  | Lata
  | Lade
  | Divsimp (* New *)
  | Prodsimp (* New *)
  | Uminussimp (* New *)
  | Minussimp (* New *)
  | Sumsimp (* New *)
  | Compsimp (* New *)
  | Larweq (* New *)
  | Bind (* New *)
  | Fins
  | Qcnf (* New *)
  | Ident (* Internal *)
  | Hole

val is_iff : SmtAtom.Form.t -> bool
val is_eq : SmtAtom.Form.t -> bool

type id = string
val id_of_string : string -> id
val string_of_id : id -> string
val generate_id : unit -> id
val generate_ids : int -> id list

val get_clause : id -> (SmtAtom.Form.t SmtCertif.clause) option
val get_clause_exception : string -> id -> SmtAtom.Form.t SmtCertif.clause
val add_clause : id -> SmtAtom.Form.t SmtCertif.clause -> unit
val clauses_to_string : string

val add_ref : string -> int -> unit
val get_ref : string -> int
val to_add : (int * SmtAtom.Form.t list) list ref

val mk_clause : id * typ * SmtAtom.Form.t list * id list * id list -> id

val apply_dec_atom : (?declare:bool -> SmtAtom.hatom -> SmtAtom.hatom) ->
                     bool * Form.atom_form_lit -> bool * Form.atom_form_lit
val apply_bdec_atom :
  (?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) ->
  bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit
val apply_tdec_atom :
  (?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) ->
  bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit

val apply_dec : ('a -> 'b) -> bool * 'a -> bool * 'b
(* From the boolean of each element, decides the boolean for the entire list *)
val list_dec : (bool * 'a) list -> bool * 'a list


val get_solver : string -> bool * Form.atom_form_lit
val add_solver : string -> bool * Form.atom_form_lit -> unit

val find_opt_qvar : string -> SmtBtype.btype option 
val add_qvar : string -> SmtBtype.btype -> unit
val clear_qvar : unit -> unit

val init_index : SmtAtom.Form.t list -> (SmtAtom.Form.t -> SmtAtom.Form.t) ->
                 SmtAtom.Form.t -> int

val qf_to_add : SmtAtom.Form.t SmtCertif.clause list -> (SmtAtom.Form.t SmtCertif.clause_kind * SmtAtom.Form.t list option * SmtAtom.Form.t SmtCertif.clause) list

val ra : SmtAtom.Atom.reify_tbl
val rf : SmtAtom.Form.reify
val ra_quant : SmtAtom.Atom.reify_tbl
val rf_quant : SmtAtom.Form.reify

val hlets : (string, Form.atom_form_lit) Hashtbl.t

val clear : unit -> unit
