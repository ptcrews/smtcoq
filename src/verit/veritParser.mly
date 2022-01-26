%{
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


  open SmtBtype
  open SmtAtom
  open SmtForm
  open VeritSyntax
  open VeritAst

  exception InvalidProofStepNo

  let symbol_to_id s = 
    (* f transforms string "tn" to int n *)
    let f = (fun s -> let l = (String.length s) - 1 in
                      int_of_string (String.sub s 1 l)) in
    (* Subproof steps have labels*)                  
    let syms = List.map f (String.split_on_char '.' s) in
    if (List.length syms == 1) then 
      List.hd syms
    else 
      raise InvalidProofStepNo

  (* transform string "@p_n" to int n *)
  let atsymbol_to_id s = 
    let l = (String.length s) - 3 in
    int_of_string (String.sub s 3 l)
    
  (* Counter for any cong rules encountered *)
  let congCtr = ref max_int

  let parse_bv s =
    let l = ref [] in
    for i = 2 to String.length s - 1 do
      match s.[i] with
      | '0' -> l := false :: !l
      | '1' -> l := true :: !l
      | _ -> assert false
    done;
    !l

%}


/*
  définition des lexèmes
*/

%token <string> SYMBOL
%token <string> ATSYMBOL
%token <string> ISYMBOL
%token <string> SPECCONST
%token <string> KEYWORD
%token <string> STRING
%token <int> INT
%token <Big_int.big_int> BIGINT

%token LPAREN RPAREN EOF EOL COLON BANG COLEQ
%token COLRULE COLSTEP COLARGS COLPREMISES SAT
%token ASSUME STEP ANCHOR DEFINEFUN CL ASTOK CHOICE
%token LET FORALL EXISTS MATCH TINT TBOOL NAMED

%token TRUE FALSE NOT IMPLIES AND OR XOR DIST ITE
%token NOTNOT
%token THRESO RESO TAUT CONT
%token REFL TRANS CONG EQRE EQTR EQCO EQCP
%token NOTOR NOTAND XOR1 XOR2 NXOR1 NXOR2 IMP NIMP1 NIMP2
%token EQU1 EQU2 NEQU1 NEQU2 ANDP ANDN ORP ORN
%token XORP1 XORP2 XORN1 XORN2 IMPP IMPN1 IMPN2
%token EQUP1 EQUP2 EQUN1 EQUN2
%token ITE1 ITE2 ITEP1 ITEP2 ITEN1 ITEN2 NITE1 NITE2
%token CONNDEF ANDSIMP ORSIMP NOTSIMP IMPSIMP
%token EQSIMP BOOLSIMP ACSIMP ITESIMP EQUALSIMP DISTELIM
%token EQ LT LEQ GT GEQ PLUS MINUS MULT
%token LAGE LIAGE LATA LADE DIVSIMP PRODSIMP 
%token UMINUSSIMP MINUSSIMP SUMSIMP COMPSIMP LARWEQ
%token FINS BIND QCNF
%token BVAND BVOR BVXOR BVADD BVMUL BVULT BVSLT BVULE 
%token BVSLE BVCONC BVEXTR BVZEXT BVSEXT BVNOT BVNEG
%token BVSHL BVSHR
%token <string> BITV
%type <int> line
%start line

%%

line:
  | LPAREN ASSUME s=SYMBOL t=term RPAREN EOL
    { mk_step (s, Assume, mk_cl [t], [], []) }
  | LPAREN STEP s=SYMBOL c=clause COLRULE r=rulename RPAREN EOL
    { mk_step (s, r, c, [], []) }
  | LPAREN STEP s=SYMBOL c=clause COLRULE r=rulename COLPREMISES LPAREN prems=SYMBOL+ RPAREN RPAREN EOL
    { mk_step (s, r, c, prems, []) }
  | LPAREN STEP s=SYMBOL c=clause COLRULE r=rulename COLPREMISES LPAREN prems=SYMBOL+ RPAREN
      COLARGS LPAREN args=arg+ RPAREN RPAREN EOL
    { mk_step (s, r, c, prems, args) }
  | LPAREN STEP s=SYMBOL c=clause COLRULE r=rulename COLARGS LPAREN args=arg+ RPAREN RPAREN EOL
    { mk_step (s, r, c, [], args) }
  (* Add anchor *)
;

arg:
  | i=INT { i }
  | LPAREN i=INT RPAREN                     { i } (* Negative ints are parameterized *)
  | LPAREN MINUS i=INT RPAREN               { (-i) }
  (*| LPAREN COLEQ sv=sorted_var s=SYMBOL RPAREN {}*)
;
  
ident:
  | s=SYMBOL                                { Var s }
  | i=ISYMBOL                               { Var i }
;

clause:
  | LPAREN CL ts=term* RPAREN               { mk_cl ts }
;

term:
  (* Shared terms *)
  | LPAREN BANG t=term NAMED a=ATSYMBOL RPAREN
    { NTerm (a, t) }
  | a=ATSYMBOL                              { STerm a }

  (* Formulas *)
  | TRUE                                    { True }
  | FALSE                                   { False }
  | LPAREN NOT t=term RPAREN                { Not l }  
  | LPAREN AND ts=term* RPAREN              { And ts }
  | LPAREN OR ts=term* RPAREN               { Or ts }
  | LPAREN IMPLIES ts=term* RPAREN          { Imp ts }
  | LPAREN XOR ts=term* RPAREN              { Xor ts }
  | LPAREN ITE c=term t1=term t2=term RPAREN
    { Ite c::t1::t2::[] }
  | LPAREN FORALL LPAREN vs=sorted_var+ RPAREN t=term RPAREN
    { Forall (vs, t) }

  (* Atoms *)
  | i=INT                                   { Int i }
  (*| b=BIGINT                              {}
  | b=BITV                                  {}*)
  | LPAREN LT x=term y=term RPAREN          { Lt (x, y) }
  | LPAREN LEQ x=term y=term RPAREN         { Leq  (x, y) }
  | LPAREN GT x=term y=term RPAREN          { Gt (x, y) }
  | LPAREN GEQ x=term y=term RPAREN         { Geq (x, y) }
  | LPAREN MINUS x=term RPAREN              { UMinus x }
  | LPAREN PLUS x=term y=term RPAREN        { Plus (x, y) }
  | LPAREN MINUS x=term y=term RPAREN       { Minus (x, y) }
  | LPAREN MULT x=term y=term RPAREN        { Mult (x, y) }
  (*| LPAREN DIST terms=term* RPAREN        {}
  | LPAREN BVNOT t=term RPAREN              {}
  | LPAREN BVAND t1=term t2=term RPAREN     {}
  | LPAREN BVOR t1=term t2=term RPAREN      {}
  | LPAREN BVXOR t1=term t2=term RPAREN     {}
  | LPAREN BVNEG t=term RPAREN              {}
  | LPAREN BVADD t1=term t2=term RPAREN     {}
  | LPAREN BVMUL t1=term t2=term RPAREN     {}
  | LPAREN BVULT t1=term t2=term RPAREN     {}
  | LPAREN BVSLT t1=term t2=term RPAREN     {}
  | LPAREN BVULE t1=term t2=term RPAREN     {}
  | LPAREN BVSLE t1=term t2=term RPAREN     {}
  | LPAREN BVSHL t1=term t2=term RPAREN     {}
  | LPAREN BVSHR t1=term t2=term RPAREN     {}
  | LPAREN BVCONC t1=term t2=term RPAREN    {}
  | LPAREN BVEXTR j=INT i=INT t=term RPAREN {}
  | LPAREN BVZEXT n=INT t=term RPAREN       {}
  | LPAREN BVSEXT n=INT t=term RPAREN       {}*)
  | i=ident                                 { i }
  | LPAREN f=SYMBOL l=term+ RPAREN          { App (f,l) }
  | LPAREN EQ t1=term t2=term RPAREN        { Eq (t1, t2) }
  (*| LPAREN LET LPAREN var_binding+ RPAREN term RPAREN { "" }
  | LPAREN EXISTS LPAREN sorted_var+ RPAREN term RPAREN { "" }
  | LPAREN MATCH term LPAREN match_case+ RPAREN RPAREN { "" }
  | LPAREN BANG term attr+ RPAREN { "" }*)
;

sort:
  | TINT                                    { Int }
  | TBOOL                                   { Bool }
;

sorted_var:
  | LPAREN s=SYMBOL t=sort RPAREN           { (s,t) }
;

rulename:
  | ASSUME                                  { Assume }
  | TRUE                                    { True }
  | FALSE                                   { Fals }
  | NOTNOT                                  { Notnot }
  | THRESO                                  { Threso }
  | RESO                                    { Reso }
  | TAUT                                    { Taut }
  | CONT                                    { Cont }
  | REFL                                    { Hole }
  | TRANS                                   { Trans }
  | CONG                                    { Cong }
  | EQRE                                    { Eqre }
  | EQTR                                    { Eqtr }
  | EQCO                                    { Eqco }
  | EQCP                                    { Eqcp }
  | AND                                     { And }
  | NOTOR                                   { Nor }
  | OR                                      { Or }
  | NOTAND                                  { Nand }
  | XOR1                                    { Xor1 }
  | XOR2                                    { Xor2 }
  | NXOR1                                   { Nxor1 }
  | NXOR2                                   { Nxor2 }
  | IMP                                     { Imp }
  | NIMP1                                   { Nimp1 }
  | NIMP2                                   { Nimp2 }
  | EQU1                                    { Equ1 }
  | EQU2                                    { Equ2 }
  | NEQU1                                   { Nequ1 }
  | NEQU2                                   { Nequ2 }
  | ANDP                                    { Andp }
  | ANDN                                    { Andn }
  | ORP                                     { Orp }
  | ORN                                     { Orn }
  | XORP1                                   { Xorp1 }
  | XORP2                                   { Xorp2 }
  | XORN1                                   { Xorn1 }
  | XORN2                                   { Xorn2 }
  | IMPP                                    { Impp }
  | IMPN1                                   { Impn1 }
  | IMPN2                                   { Impn2 }
  | EQUP1                                   { Equp1 }
  | EQUP2                                   { Equp2 }
  | EQUN1                                   { Equn1 }
  | EQUN2                                   { Equn2 }
  | ITE1                                    { Ite1 }
  | ITE2                                    { Ite2 }
  | ITEP1                                   { Itep1 }
  | ITEP2                                   { Itep2 }
  | ITEN1                                   { Iten1 }
  | ITEN2                                   { Iten2 }
  | NITE1                                   { Nite1 }
  | NITE2                                   { Nite2 }
  | CONNDEF                                 { Conndef }
  | ANDSIMP                                 { Andsimp }
  | ORSIMP                                  { Orsimp }
  | NOTSIMP                                 { Notsimp }
  | IMPSIMP                                 { Impsimp }
  | EQSIMP                                  { Eqsimp }
  | BOOLSIMP                                { Boolsimp }
  | ACSIMP                                  { Hole }
  | ITESIMP                                 { Itesimp }
  | EQUALSIMP                               { Eqsimp }
  | DISTELIM                                { Distelim }
  | LAGE                                    { Lage }
  | LIAGE                                   { Liage }
  | LATA                                    { Lata} 
  | LADE                                    { Lade }
  | DIVSIMP                                 { Divsimp } 
  | PRODSIMP                                { Prodsimp }
  | UMINUSSIMP                              { Uminussimp }
  | MINUSSIMP                               { Minussimp }
  | SUMSIMP                                 { Sumsimp }
  | COMPSIMP                                { Compsimp }
  | LARWEQ                                  { Larweq }

(*function_def:
  | SYMBOL LPAREN sorted_var* RPAREN sort term { "" }
;

var_binding:
  | LPAREN SYMBOL term RPAREN { "" }
;
pattern:
  | SYMBOL { "" }
  | LPAREN SYMBOL SYMBOL+ RPAREN { "" }
;

match_case:
  | LPAREN pattern term RPAREN { "" }
;*)