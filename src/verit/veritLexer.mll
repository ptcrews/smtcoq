{
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


  open VeritParser

  let typ_table = Hashtbl.create 53
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add typ_table kwd tok)
      [
      (* SMTLIB formulas *)
        "true", TRUE;
        "false", FALSE;
        "not", NOT;
        "=>", IMPLIES;
        "and", AND;
        "or", OR;
        "xor", XOR;
        "ite", ITE;
        "distinct", DIST;

      (*Basic proof rules*)
        "assume", ASSUME;
        (*true*)
        (*false*)
        "not_not", NOTNOT;

      (* Resolution rules and clause simplifications *)
        "th_resolution", THRESO;
        "resolution", RESO;
        "tautology", TAUT;
        "contraction", CONT;

      (* Equality and congruence reasoning rules *)
        "refl", REFL;
        "trans", TRANS;
        "cong", CONG;
        "eq_reflexive", EQRE;
        "eq_transitive", EQTR;
        "eq_congruent", EQCO;
        "eq_congruent_pred", EQCP;

      (* Clausification of Boolean operators rules *)
        (*and*)
        "not_or", NOTOR;
        (*or*)
        "not_and", NOTAND;
        "xor1", XOR1;
        "xor2", XOR2;
        "not_xor1", NXOR1;
        "not_xor2", NXOR2;
        "implies", IMP;
        "not_implies1", NIMP1;
        "not_implies2", NIMP2;
        "equiv1", EQU1;
        "equiv2", EQU2;
        "not_equiv1", NEQU1;
        "not_equiv2", NEQU2;
        "and_pos", ANDP;
        "and_neg", ANDN;
        "or_pos", ORP;
        "or_neg", ORN;
        "xor_pos1", XORP1;
        "xor_pos2", XORP2;
        "xor_neg1", XORN1;
        "xor_neg2", XORN2;
        "implies_pos", IMPP;
        "implies_neg1", IMPN1;
        "implies_neg2", IMPN2;
        "equiv_pos1", EQUP1;
        "equiv_pos2", EQUP2;
        "equiv_neg1", EQUN1;
        "equiv_neg2", EQUN2;

      (* Clausification of ITE rules *)
        "ite1", ITE1;
        "ite2", ITE2;
        "ite_pos1", ITEP1;
        "ite_pos2", ITEP2;
        "ite_neg1", ITEN1;
        "ite_neg2", ITEN2;
        "not_ite1", NITE1;
        "not_ite2", NITE2;

      (* cvc5 rules *)
        "symm", SYMM;
        "reordering", REORD;
        "all_simplify", ALLSIMP;

      (* Simplifications on Boolean operators rules *)
        "connective_def", CONNDEF;
        "and_simplify", ANDSIMP;
        "or_simplify", ORSIMP;
        "not_simplify", NOTSIMP;
        "implies_simplify", IMPSIMP;
        "equiv_simplify", EQSIMP;
        "bool_simplify", BOOLSIMP;
        "ac_simp", ACSIMP;
        "distinct_elim", DISTELIM;

      (* Simplifications on ITE operators rules *)
        "ite_simplify", ITESIMP;

      (* Simplifications on equalities rules *)
        "eq_simplify", EQUALSIMP;

      (* Quantifier rules *)
        "bind", BIND;
        "forall_inst", FINS;
        "qnt_cnf", QCNF;

      (* Linear Integer Arithmetic rules *)
        "la_generic", LAGE;
        "lia_generic", LIAGE;
        "la_tautology", LATA;
        "la_disequality", LADE;
        "div_simplify", DIVSIMP;
        "prod_simplify", PRODSIMP;
        "unary_minus_simplify", UMINUSSIMP;
        "minus_simplify", MINUSSIMP;
        "sum_simplify", SUMSIMP;
        "comp_simplify", COMPSIMP;
        "la_rw_eq", LARWEQ;

      (* Subproofs *)
        "subproof", SUBPROOF;
      

      (* Bit-vector Rules *)
        (*"bbvar", BBVA;
        "bbconst", BBCONST;
        "bbeq", BBEQ;
        "bv_const_neq", BBDIS;
        "bbop", BBOP;
        "bbnot", BBNOT;
        "bbneg", BBNEG;
        "bbadd", BBADD;
        "bbmul", BBMUL;
        "bbult", BBULT;
        "bbslt", BBSLT;
        "bbconcat", BBCONC;
        "bbextract", BBEXTR;
        "bbzextend", BBZEXT;
        "bbsextend", BBSEXT;
        "bbshl", BBSHL;
        "bbshr", BBSHR;
        "bvand", BVAND;
        "bvor", BVOR;
        "bvxor", BVXOR;
        "bvadd", BVADD;
        "bvmul", BVMUL;
        "bvult", BVULT;
        "bvslt", BVSLT;
        "bvule", BVULE;
        "bvsle", BVSLE;
        "bvshl", BVSHL;
        "bvlshr", BVSHR;
        "bvnot", BVNOT;
        "bvneg", BVNEG;
        "concat", BVCONC;
        "extract", BVEXTR;
        "zero_extend", BVZEXT;
        "sign_extend", BVSEXT;*)
      ]
}

(*
let digit = [ '0'-'9' ]*)
let bit = [ '0'-'1' ]
let bitvector = '#' 'b' bit+
(*let alpha = [ 'a'-'z' 'A' - 'Z' ]
let blank = [' ' '\t']
let newline = ['\n' '\r']
let var = alpha (alpha|digit|'_')*
let atvar = '@' var
let bindvar = '?' var+
let int = '-'? digit+
*)
let newline = '\r' | '\n' | "\r\n"
let blank = [' ' '\009']
let wspace = ['\009' '\010' '\013' '\032']
let printable_char = ['\032'-'\126' '\128'-'\255']
let digit = ['0'-'9']
let non_zero_digit = ['1'-'9']
let hexdigit = digit | ['a'-'f' 'A'-'F']
let bindigit = ['0'-'1']
let letter = ['a'-'z' 'A'-'Z']
let spl = [ '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' ]
let int = '-'? digit+

let simple_symbol = (letter | spl) (letter | digit | spl)*
let at_symbol = '@' simple_symbol
let symbol = simple_symbol | '|' (wspace | printable_char # ['|' '\\'])* '|'
let numeral = '0' | non_zero_digit digit*
(*let decimal = numeral '.' '0'* numeral
let hexadecimal = '#' 'x' hexdigit+
let binary = '#' 'b' bindigit+
let qstring = '"' (wspace | printable_char)* '"'
let spec_constant = numeral | decimal | hexadecimal | binary | qstring*)
let index = numeral | symbol
let isymbol = '(' '_' symbol index+ ')'
let keyword = ':' simple_symbol

rule token = parse
  | blank +                     { token lexbuf }
  | newline                     { Lexing.new_line lexbuf;
                                  EOL }
  | "("                         { LPAREN }
  | ")"                         { RPAREN }
  | ":"                         { COLON }
  | "!"                         { BANG }
  | ":rule"                     { COLRULE }
  | ":step"                     { COLSTEP }
  | ":args"                     { COLARGS }
  | ":premises"                 { COLPREMISES }
  | ":discharge"                { COLDISCHARGE }
  | ":named"                    { NAMED }
  | "assume"                    { ASSUME }
  | "step"                      { STEP }
  | "anchor"                    { ANCHOR }
  | "define_fun"                { DEFINEFUN }
  | "cl"                        { CL }
  | "as"                        { ASTOK }
  | "choice"                    { CHOICE }
  | "let"                       { LET }
  | "forall"                    { FORALL }
  | "exists"                    { EXISTS }
  | "match"                     { MATCH }
  | "="                         { EQ }
  | "<"                         { LT }
  | "<="                        { LEQ }
  | ">"                         { GT }
  | ">="                        { GEQ }
  | "+"                         { PLUS }
  | "-"                         { MINUS }
  | "*"                         { MULT }
  | "Int"     	      	        { TINT }
  | "Bool"		                  { TBOOL }
  | ":="                        { COLEQ }
  | keyword                     { let k = Lexing.lexeme lexbuf in 
                                  try Hashtbl.find typ_table k with
                                  | Not_found -> KEYWORD k }
  | symbol                      { let s = Lexing.lexeme lexbuf in 
                                  try Hashtbl.find typ_table s with
                                  | Not_found -> SYMBOL s }
  | at_symbol                   { let s = Lexing.lexeme lexbuf in
                                  try Hashtbl.find typ_table s with
                                  | Not_found -> ATSYMBOL s }
  | isymbol                     { let i = Lexing.lexeme lexbuf in 
                                  ISYMBOL i }
  | (int as i)                  { try INT (int_of_string i) with 
                                  _ -> BIGINT (Big_int.big_int_of_string i) }
(*  | bitvector as bv             { BITV bv }*)
  | eof                         { EOF }
