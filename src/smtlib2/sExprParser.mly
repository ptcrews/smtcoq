%{
(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* Parser for S-expressions
   
   Code lightly adapted from the OCaml sexplib, which is part of the
   ocaml-core alternative standard library for OCaml.

*)

  (** Parser: Grammar Specification for Parsing S-expressions *)

  open Lexing

  let parse_failure what =
    let pos = symbol_start_pos () in
    let msg =
      Printf.sprintf "SExprParser: failed to parse line %d char %d: %s"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol) what in
    failwith msg
%}

%token <string> STRING
%token LPAREN RPAREN /*CVC5 INTERRUPTED BY TIMEOUT*/ CVC5_TIMEOUT CORE_DUMPED HASH_SEMI EOF

%start sexp
%type <SExpr.t> sexp

%start sexp_opt
%type <SExpr.t option> sexp_opt

%start sexps
%type <SExpr.t list> sexps

%start rev_sexps
%type <SExpr.t list> rev_sexps

%%

sexp:
| sexp_comments sexp_but_no_comment { $2 }
| sexp_but_no_comment { $1 }

sexp_but_no_comment
  : CVC5_TIMEOUT { SExpr.List [SExpr.Atom "cvc5_timeout"] }
  | CORE_DUMPED { SExpr.List [SExpr.Atom "cvc5_timeout"] }
  | STRING { SExpr.Atom $1 }
  | LPAREN RPAREN { SExpr.List [] }
  | LPAREN rev_sexps_aux RPAREN { SExpr.List (List.rev $2) }
  
  /*| CVC5 INTERRUPTED BY TIMEOUT { SExpr.List [SExpr.Atom "cvc5_timeout"] }*/
  /*| STRING LPAREN STRING STRING RPAREN { SExpr.List [SExpr.Atom $1; SExpr.Atom $3; SExpr.Atom $4] }*/
  | error { parse_failure "sexp" }

sexp_comment
  : HASH_SEMI sexp_but_no_comment { () }
  | HASH_SEMI sexp_comments sexp_but_no_comment { () }

sexp_comments
  : sexp_comment { () }
  | sexp_comments sexp_comment { () }

sexp_opt
  : sexp_but_no_comment { Some $1 }
  | sexp_comments sexp_but_no_comment { Some $2 }
  | EOF { None }
  | sexp_comments EOF { None }

rev_sexps_aux
  : sexp_but_no_comment { [$1] }
  | sexp_comment { [] }
  | rev_sexps_aux sexp_but_no_comment { $2 :: $1 }
  | rev_sexps_aux sexp_comment { $1 }

rev_sexps
  : rev_sexps_aux EOF { $1 }
  | EOF { [] }

sexps
  : rev_sexps_aux EOF { List.rev $1 }
  | EOF { [] }
