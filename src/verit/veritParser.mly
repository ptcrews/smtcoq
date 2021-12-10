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
%token <string> ISYMBOL
%token <string> SPECCONST
%token <string> KEYWORD
%token <string> STRING
%token <int> INT
%token <Big_int.big_int> BIGINT

%token LPAREN RPAREN EOF EOL COLON BANG
%token COLRULE COLSTEP COLARGS COLPREMISES SAT
%token ASSUME STEP ANCHOR DEFINEFUN CL ASTOK CHOICE
%token LET FORALL EXISTS MATCH TINT TBOOL

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
%token FINS
%token BVAND BVOR BVXOR BVADD BVMUL BVULT BVSLT BVULE 
%token BVSLE BVCONC BVEXTR BVZEXT BVSEXT BVNOT BVNEG
%token BVSHL BVSHR
%token <string> BITV
%type <int> line
%start line

%%

line:
  | SAT EOL { raise Sat }
  | LPAREN ASSUME s=SYMBOL l=lit RPAREN EOL
    { let id = symbol_to_id s in
      let _, l' = l in
      mk_clause (id, Assume, [l'], [], []) }
  | LPAREN STEP s=SYMBOL c=clause COLRULE r=rulename RPAREN EOL
    { let id = symbol_to_id s in
        mk_clause (id, r, c, [], []) }
  | LPAREN STEP s=SYMBOL c=clause COLRULE r=rulename COLPREMISES LPAREN prems=SYMBOL+ RPAREN RPAREN EOL
    { let id = symbol_to_id s in
      let prems' = List.map symbol_to_id prems in
      match r with
      (* For the congruence rule, that internally uses EqCongr and Resolution, we 
         maintain a separate id counter to store the result of the EqCongr application,
         this id counter is passed as an argument since the Cong rule takes no arguments  *)
      | Cong -> 
          let arg = !congCtr in
            congCtr := !congCtr - 1;
            mk_clause (id, r, c, prems', [arg])
      | _ -> mk_clause (id, r, c, prems', []) }
  | LPAREN STEP s=SYMBOL c=clause COLRULE r=rulename COLPREMISES LPAREN prems=SYMBOL+ RPAREN
      COLARGS LPAREN args=par+ RPAREN RPAREN EOL
    { let id = symbol_to_id s in
      let prems' = List.map symbol_to_id prems in
      mk_clause (id, r, c, prems', args) }
  | LPAREN STEP s=SYMBOL c=clause COLRULE r=rulename COLARGS LPAREN args=par+ RPAREN RPAREN EOL
    { let id = symbol_to_id s in
      mk_clause (id, r, c, [], args) }
  /*| LPAREN ANCHOR COLSTEP SYMBOL RPAREN { "" }
  | LPAREN ANCHOR COLSTEP SYMBOL COLARGS proof_args RPAREN { "" }
  | LPAREN DEFINEFUN function_def RPAREN { "" }*/
;

par:
  | i=INT { i }
  | LPAREN i=INT RPAREN { i } (* Negative ints are parameterized *)
  | LPAREN MINUS i=INT RPAREN { (-i) }
;

/*sexpr:
  | SYMBOL { "" }
  | KEYWORD { "" }
  | LPAREN sexpr* RPAREN { "" }
;

attr_val:
  | SPECCONST { "" }
  | SYMBOL { "" }
  | LPAREN sexpr* RPAREN { "" }
;

attr:
  | KEYWORD { "" }
  | KEYWORD attr_val { "" }
;*/

ident:
  | s=SYMBOL 
  { match find_opt_qvar s with
    | Some bt   -> false, Form.Atom (Atom.get ~declare:false ra (Aapp (dummy_indexed_op (Rel_name s) [||] bt, [||])))
    | None      -> true, Form.Atom (Atom.get ra (Aapp (SmtMaps.get_fun s, [||]))) }
  | i=ISYMBOL
  { match find_opt_qvar i with
    | Some bt   -> false, Form.Atom (Atom.get ~declare:false ra (Aapp (dummy_indexed_op (Rel_name i) [||] bt, [||])))
    | None      -> true, Form.Atom (Atom.get ra (Aapp (SmtMaps.get_fun i, [||]))) }
;

qual_id:
  | i=ident { i }
  /*| LPAREN AS ident sort RPAREN { "" }*/
;

clause:
  | LPAREN CL lits=lit* RPAREN
    { let _, l = list_dec lits in l }
;

lit:   /* returns a SmtAtom.Form.t option */
  | t=term
  { let decl, t' = t in 
      decl, Form.lit_of_atom_form_lit rf (decl, t') 
  }
  | LPAREN NOT l=lit RPAREN       { apply_dec Form.neg l }
(*{
    let decl, l' = l in
    if Form.is_pos l' then
      decl, Form.neg l'
    else
      let f = Form.Form (Fapp (Fnot2 1, Array.make 1 (Form.neg l'))) in
      decl, (Form.lit_of_atom_form_lit rf (decl, f))
  }*)
;

nlit:
  | LPAREN NOT l=lit RPAREN       { apply_dec Form.neg l }
(*{ Parse double negations as Fnot2 instead of simplifying
    let decl, l' = l in
    if Form.is_pos l' then
      decl, Form.neg l'
    else
      let f = Form.Form (Fapp (Fnot2 1, Array.make 1 (Form.neg l'))) in
      decl, (Form.lit_of_atom_form_lit rf (decl, f))
  }*)
;

(*term:   /* returns a bool * (SmtAtom.Form.pform or a SmtAtom.hatom), the boolean indicates if we should declare the term or not */
  (*| b=BITV                        { true, Form.Atom (Atom.mk_bvconst ra (parse_bv b)) }*)
  | TRUE                            { true, Form.Form Form.pform_true }
  | FALSE                           { true, Form.Form Form.pform_false }
  | q=qual_id                       { q }
  (*| b=BINDVAR                     { true, Hashtbl.find hlets b }*)
  | i=INT                           { true, Form.Atom (Atom.hatom_Z_of_int ra i) }
  | i=BIGINT                        { true, Form.Atom (Atom.hatom_Z_of_bigint ra i) }
;*)

term: /* returns a bool * (SmtAtom.Form.pform or SmtAtom.hatom), the boolean indicates if we should declare the term or not */
  (* This will make term produce shift-reduce conflicts, and seems unnecessary
  | LPAREN t=term RPAREN            { t }*)

  (* Formulas *)
  | TRUE                            { true, Form.Form Form.pform_true }
  | FALSE                           { true, Form.Form Form.pform_false }
  | LPAREN AND lits=lit* RPAREN
    { apply_dec (fun x -> Form.Form (Fapp (Fand, Array.of_list x))) 
                (list_dec lits) }
  | LPAREN OR lits=lit* RPAREN
    { apply_dec (fun x -> Form.Form (Fapp (For, Array.of_list x))) 
                (list_dec lits) }
  | LPAREN IMPLIES lits=lit* RPAREN
    { apply_dec (fun x -> Form.Form (Fapp (Fimp, Array.of_list x))) 
                (list_dec lits) }
  | LPAREN XOR lits=lit* RPAREN
    { apply_dec (fun x -> Form.Form (Fapp (Fxor, Array.of_list x))) 
                (list_dec lits) }
  | LPAREN ITE lits=lit* RPAREN
    { apply_dec (fun x -> Form.Form (Fapp (Fite, Array.of_list x))) 
                (list_dec lits) }
  | LPAREN FORALL LPAREN vs=sorted_var+ RPAREN q=qlit RPAREN
    { clear_qvar (); (*List.fold_left (fun (s, t) -> add_qvar s t) () vs;*)
      false, Form.Form (Fapp (Fforall vs, [|Form.lit_of_atom_form_lit rf q|])) }

  (* Atoms *)
  | i=INT                             { true, Form.Atom (Atom.hatom_Z_of_int ra i) }
  | b=BIGINT                          { true, Form.Atom (Atom.hatom_Z_of_bigint ra b) }
  | b=BITV                              { true, Form.Atom (Atom.mk_bvconst ra (parse_bv b)) }
  | LPAREN LT x=term y=term RPAREN    { apply_bdec_atom (Atom.mk_lt ra) x y }
  | LPAREN LEQ x=term y=term RPAREN   { apply_bdec_atom (Atom.mk_le ra) x y }
  | LPAREN GT x=term y=term RPAREN    { apply_bdec_atom (Atom.mk_gt ra) x y }
  | LPAREN GEQ x=term y=term RPAREN   { apply_bdec_atom (Atom.mk_ge ra) x y }
  | LPAREN PLUS x=term y=term RPAREN  { apply_bdec_atom (Atom.mk_plus ra) x y }
  | LPAREN MULT x=term y=term RPAREN  { apply_bdec_atom (Atom.mk_mult ra) x y }
  | LPAREN MINUS x=term y=term RPAREN { apply_bdec_atom (Atom.mk_minus ra) x y }
  | LPAREN MINUS x=term RPAREN        { apply_dec_atom (fun ?declare:d a -> Atom.mk_neg ra a) x }
  (*| OPP x=term                      { apply_dec_atom (Atom.mk_opp ra) x }*)
  | LPAREN DIST terms=term* RPAREN
    { let args = List.map (fun x -> (match x with
                | decl, Form.Atom h -> (decl, h)
                | _ -> assert false)) terms in
      let da, la = list_dec args in
    	let a = Array.of_list la in
        da, Form.Atom (Atom.mk_distinct ra ~declare:da (Atom.type_of a.(0)) a) }
  | LPAREN BVNOT t=term RPAREN
    { apply_dec_atom (fun ?declare:(d=true) h -> 
                     match Atom.type_of h with 
                     | TBV s -> Atom.mk_bvnot ra ~declare:d s h 
                     | _ -> assert false) 
      t }
  | LPAREN BVAND t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> 
                       match Atom.type_of h1 with 
                       | TBV s -> Atom.mk_bvand ra ~declare:d s h1 h2
                       | _ -> assert false)
      t1 t2 }
  | LPAREN BVOR t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> 
                       match Atom.type_of h1 with 
                       | TBV s -> Atom.mk_bvor ra ~declare:d s h1 h2
                       | _ -> assert false)
      t1 t2 }
  | LPAREN BVXOR t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> 
                       match Atom.type_of h1 with 
                       | TBV s -> Atom.mk_bvxor ra ~declare:d s h1 h2 
                       | _ -> assert false) 
      t1 t2 }
  | LPAREN BVNEG t=term RPAREN
    { apply_dec_atom (fun ?declare:(d=true) h -> 
                      match Atom.type_of h with 
                      | TBV s -> Atom.mk_bvneg ra ~declare:d s h
                      | _ -> assert false)
      t }
  | LPAREN BVADD t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 ->
                       match Atom.type_of h1 with
                       | TBV s -> Atom.mk_bvadd ra ~declare:d s h1 h2
                       | _ -> assert false)
      t1 t2 }
  | LPAREN BVMUL t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 ->
                       match Atom.type_of h1 with
                       | TBV s -> Atom.mk_bvmult ra ~declare:d s h1 h2
                       | _ -> assert false)
      t1 t2 }
  | LPAREN BVULT t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 ->
                       match Atom.type_of h1 with
                       | TBV s -> Atom.mk_bvult ra ~declare:d s h1 h2
                       | _ -> assert false)
      t1 t2 }
  | LPAREN BVSLT t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> 
                       match Atom.type_of h1 with
                       | TBV s -> Atom.mk_bvslt ra ~declare:d s h1 h2
                       | _ -> assert false)
      t1 t2 }
  | LPAREN BVULE t1=term t2=term RPAREN
    { let (decl,_) as a = apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> 
                                           match Atom.type_of h1 with 
                                           | TBV s -> Atom.mk_bvult ra ~declare:d s h1 h2 
                                           | _ -> assert false) 
                          t1 t2 in 
      (decl, Form.Lit (Form.neg (Form.lit_of_atom_form_lit rf a))) }
  | LPAREN BVSLE t1=term t2=term RPAREN
    { let (decl,_) as a = apply_bdec_atom (fun ?declare:(d=true) h1 h2 ->
                                           match Atom.type_of h1 with 
                                           | TBV s -> Atom.mk_bvslt ra ~declare:d s h1 h2
                                           | _ -> assert false) 
                          t1 t2 in
      (decl, Form.Lit (Form.neg (Form.lit_of_atom_form_lit rf a))) }
  | LPAREN BVSHL t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 ->
                       match Atom.type_of h1 with
                      | TBV s -> Atom.mk_bvshl ra ~declare:d s h1 h2
                      | _ -> assert false)
      t1 t2 }
  | LPAREN BVSHR t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 ->
                       match Atom.type_of h1 with
                       | TBV s -> Atom.mk_bvshr ra ~declare:d s h1 h2
                       | _ -> assert false)
      t1 t2 }
  | LPAREN BVCONC t1=term t2=term RPAREN
    { apply_bdec_atom (fun ?declare:(d=true) h1 h2 ->
                       match Atom.type_of h1, Atom.type_of h2 with
                       | TBV s1, TBV s2 -> Atom.mk_bvconcat ra ~declare:d s1 s2 h1 h2
                       | _, _ -> assert false)
      t1 t2 }
  | LPAREN BVEXTR j=INT i=INT t=term RPAREN
    { apply_dec_atom (fun ?declare:(d=true) h ->
                      match Atom.type_of h with
                      | TBV s -> Atom.mk_bvextr ra ~declare:d ~s ~i ~n:(j-i+1) h
                      | _ -> assert false)
      t }
  | LPAREN BVZEXT n=INT t=term RPAREN
    { apply_dec_atom (fun ?declare:(d=true) h ->
                      match Atom.type_of h with
                      | TBV s -> Atom.mk_bvzextn ra ~declare:d ~s ~n h
                      | _ -> assert false)
      t }
  | LPAREN BVSEXT n=INT t=term RPAREN
    { apply_dec_atom (fun ?declare:(d=true) h ->
                      match Atom.type_of h with
                      | TBV s -> Atom.mk_bvsextn ra ~declare:d ~s ~n h
                      | _ -> assert false) 
      t }        

  (* Both formulas and atoms *)
  | q=qual_id                       { q }
  | LPAREN f=SYMBOL l=term+ RPAREN
    { let args = List.map (fun x -> match x with 
                                    | decl, Form.Atom h -> (decl, h) (* does this mean we can't parse applications of user-defined predicate symbols? *)
                                    | _ -> assert false)
                          l in
      match find_opt_qvar f with 
      | Some bt -> let op = dummy_indexed_op (Rel_name f) [||] bt in 
                   false, Form.Atom (Atom.get ~declare:false ra (Aapp (op, Array.of_list (snd (list_dec args))))) 
      | None ->    let dl, l = list_dec args in 
                   dl, Form.Atom (Atom.get ra ~declare:dl (Aapp (SmtMaps.get_fun f, Array.of_list l))) }
  | LPAREN EQ t1=term t2=term RPAREN
  { match t1,t2 with 
    | (decl1, Form.Atom h1), (decl2, Form.Atom h2) when 
          (match Atom.type_of h1 with 
          | SmtBtype.Tbool -> false 
          | _ -> true) -> let decl = decl1 && decl2 in 
      decl, Form.Atom (Atom.mk_eq_sym ra ~declare:decl (Atom.type_of h1) h1 h2) 
    | (decl1, t1), (decl2, t2) -> decl1 && decl2, Form.Form (Fapp (Fiff, [|Form.lit_of_atom_form_lit rf (decl1, t1); 
                                                                   Form.lit_of_atom_form_lit rf (decl2, t2)|])) 
  }
  | LPAREN EQ n=nlit l=lit RPAREN
  { match n,l with 
    (decl1, t1), (decl2, t2) -> decl1 && decl2, Form.Form (Fapp (Fiff, [|t1; t2|])) 
  }
  | LPAREN EQ t=term n=nlit RPAREN
  { match t, n with 
    | (decl1, t1), (decl2, t2) -> decl1 && decl2, Form.Form (Fapp (Fiff, [|Form.lit_of_atom_form_lit rf (decl1, t1); t2|])) 
  }
  /*
  | LPAREN LET LPAREN var_binding+ RPAREN term RPAREN { "" }
  | LPAREN EXISTS LPAREN sorted_var+ RPAREN term RPAREN { "" }
  | LPAREN MATCH term LPAREN match_case+ RPAREN RPAREN { "" }
  | LPAREN BANG term attr+ RPAREN { "" }*/
;

qlit:
  | t=term                          { t }
  | LPAREN NOT l=lit RPAREN         { apply_dec (fun x -> Form.Lit (Form.neg x)) l}

sort:
  | TINT                            { TZ }
  | TBOOL                           { Tbool }
;

sorted_var:
  | LPAREN s=SYMBOL t=sort RPAREN   { add_qvar s t; (s,t) }
;

/*function_def:
  | SYMBOL LPAREN sorted_var* RPAREN sort term { "" }
;*/

/*var_binding:
  | LPAREN SYMBOL term RPAREN { "" }
;*/
 
/*pattern:
  | SYMBOL { "" }
  | LPAREN SYMBOL SYMBOL+ RPAREN { "" }
;*/

/*match_case:
  | LPAREN pattern term RPAREN { "" }
;*/

rulename: 
  | ASSUME                          { Assume } /* Inpu */
  | TRUE                            { True }
  | FALSE                           { Fals }
  | NOTNOT                          { Notnot }
  | THRESO                          { Threso }
  | RESO                            { Reso }
  | TAUT                            { Taut } /* Needs to be checked */
  | CONT                            { Cont } /* Needs to be checked */
  | REFL                            { Hole } /* Needs to be updated */
  | TRANS                           { Trans }
  | CONG                            { Cong } /* Needs to be updated */
  | EQRE                            { Eqre }
  | EQTR                            { Eqtr }
  | EQCO                            { Eqco }
  | EQCP                            { Eqcp }
  | AND                             { And }
  | NOTOR                           { Nor }
  | OR                              { Or }
  | NOTAND                          { Nand }
  | XOR1                            { Xor1 }
  | XOR2                            { Xor2 }
  | NXOR1                           { Nxor1 }
  | NXOR2                           { Nxor2 }
  | IMP                             { Imp }
  | NIMP1                           { Nimp1 }
  | NIMP2                           { Nimp2 }
  | EQU1                            { Equ1 }
  | EQU2                            { Equ2 }
  | NEQU1                           { Nequ1 }
  | NEQU2                           { Nequ2 }
  | ANDP                            { Andp }
  | ANDN                            { Andn }
  | ORP                             { Orp }
  | ORN                             { Orn }
  | XORP1                           { Xorp1 }
  | XORP2                           { Xorp2 }
  | XORN1                           { Xorn1 }
  | XORN2                           { Xorn2 }
  | IMPP                            { Impp }
  | IMPN1                           { Impn1 }
  | IMPN2                           { Impn2 }
  | EQUP1                           { Equp1 }
  | EQUP2                           { Equp2 }
  | EQUN1                           { Equn1 }
  | EQUN2                           { Equn2 }
  | ITE1                            { Ite1 }
  | ITE2                            { Ite2 }
  | ITEP1                           { Itep1 }
  | ITEP2                           { Itep2 }
  | ITEN1                           { Iten1 }
  | ITEN2                           { Iten2 }
  | NITE1                           { Nite1 }
  | NITE2                           { Nite2 }
  | CONNDEF                         { Conndef } /* Needs to be checked */
  | ANDSIMP                         { Andsimp }
  | ORSIMP                          { Orsimp }
  | NOTSIMP                         { Notsimp }
  | IMPSIMP                         { Impsimp } /* Needs to be checked */
  | EQSIMP                          { Eqsimp } /* Needs to be checked */
  | BOOLSIMP                        { Boolsimp } /* Needs to be checked */
  | ACSIMP                          { Hole } /* Needs to be updated */
  | ITESIMP                         { Itesimp } /* Needs to be checked */
  | EQUALSIMP                       { Eqsimp } /* Needs to be checked */
  | DISTELIM                        { Distelim }
  | LAGE                            { Lage }
  | LIAGE                           { Liage }
  | LATA                            { Lata} 
  | LADE                            { Lade }
  | DIVSIMP                         { Divsimp } 
  | PRODSIMP                        { Prodsimp }
  | UMINUSSIMP                      { Uminussimp }
  | MINUSSIMP                       { Minussimp }
  | SUMSIMP                         { Sumsimp }
  | COMPSIMP                        { Compsimp }
  | LARWEQ                          { Larweq }