(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2020                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* Since ZChaff does not allow to choose where the trace is outputted,
   we use a global mutex to prevent two parallel calls to ZChaff *)

val lock_zchaff_mutex : unit -> unit
val unlock_zchaff_mutex : unit -> unit


(* TODO: when native-coq is not supported anymore, put here the list of
   lemmas from g_smtcoq *)
