open SmtBtype
open SmtAtom
open SmtForm
open VeritSyntax



(* AST: a certificate is a list of steps *)

type typ = 
  | Int
  | Bool
  | Unintr of string

type term =
  | True
  | False
  | Not of term
  | And of term list
  | Or of term list
  | Imp of term list
  | Xor of term list
  | Ite of term list
  | Forall of (string * typ) list * term
  | Eq of term * term
  | App of string * (term list)
  | Var of string
  | STerm of string (* Shared term *)
  | NTerm of string * term (* Named term *)
  | Int of int (* change to bigint *)
  | Lt of term * term
  | Leq of term * term
  | Gt of term * term
  | Geq of term * term
  | UMinus of term
  | Plus of term * term
  | Minus of term * term
  | Mult of term * term

type clause = term list
type id = string
type params = id list
type args = string list
type rule = 
  | AssumeAST
  | TrueAST
  | FalsAST
  | NotnotAST
  | ThresoAST
  | ResoAST
  | TautAST
  | ContAST
  | ReflAST
  | TransAST
  | CongAST
  | EqreAST
  | EqtrAST
  | EqcoAST
  | EqcpAST
  | AndAST
  | NorAST
  | OrAST
  | NandAST
  | Xor1AST
  | Xor2AST
  | Nxor1AST
  | Nxor2AST
  | ImpAST
  | Nimp1AST
  | Nimp2AST
  | Equ1AST
  | Equ2AST
  | Nequ1AST
  | Nequ2AST
  | AndpAST
  | AndnAST
  | OrpAST
  | OrnAST
  | Xorp1AST
  | Xorp2AST
  | Xorn1AST
  | Xorn2AST
  | ImppAST
  | Impn1AST
  | Impn2AST
  | Equp1AST
  | Equp2AST
  | Equn1AST
  | Equn2AST
  | Ite1AST
  | Ite2AST
  | Itep1AST
  | Itep2AST
  | Iten1AST
  | Iten2AST
  | Nite1AST
  | Nite2AST
  | ConndefAST
  | AndsimpAST
  | OrsimpAST
  | NotsimpAST
  | ImpsimpAST
  | EqsimpAST
  | BoolsimpAST
  | AcsimpAST
  | ItesimpAST
  | EqualsimpAST
  | DistelimAST
  | LageAST
  | LiageAST
  | LataAST
  | LadeAST
  | DivsimpAST
  | ProdsimpAST
  | UminussimpAST
  | MinussimpAST
  | SumsimpAST
  | CompsimpAST
  | LarweqAST
  | BindAST
  | FinsAST
  | QcnfAST
  | AnchorAST
  | AllsimpAST
  | SameAST
  | DischargeAST
  | SubproofAST of certif
and step = id * rule * clause * params * args
and certif = step list

let mk_cl (ts : term list) : clause = ts
let mk_step (s : (id * rule * clause * params * args)) : step = s
let mk_cert (c : step list) : certif = c
(*let mk_args (a : id list) : args = a*)


(* We will use an option type that can pass a string to print in 
   the none case
type 'a optstring =
  | Some of 'a
  | None of string

let bind o f s =
  match o with
  | Some x -> f x
  | None s' -> None (s^s')

let ( >>= ) o f s = bind o f s

(* Return the clause corresponding to the id from a certif *)
let rec get_cl (i : id) (c : certif) : clause optstring = 
  match c with
  | (i', r, c, p, a) :: t -> if i = i' then Some c else get_cl i t
  | [] -> None ("|get_cl: couldn't find "^i^"|")*)

(* Return the clause corresponding to the id from a certif *)
let rec get_cl (i : id) (c : certif) : clause option = 
  match c with
  | (i', r, c, p, a) :: t -> if i = i' then Some c else get_cl i t
  | [] -> None


(* Convert certificates to strings for debugging *)

let rec string_of_certif (c : certif) : string = 
  match c with
  | (i, r, c, p, a) :: t -> 
      let r' = string_of_rule r in
      let c' = string_of_clause c in
      let p' = List.fold_left concat_sp "" p in
      let a' = List.fold_left concat_sp "" a in
      "("^i^", "^r'^", "^c'^", ["^p'^"], ["^a'^"])\n"^(string_of_certif t)
  | [] -> ""
and string_of_rule (r : rule) : string =
  match r with
  | AssumeAST -> "AssumeAST"
  | TrueAST -> "TrueAST"
  | FalsAST -> "FalsAST"
  | NotnotAST -> "NotnotAST"
  | ThresoAST -> "ThresoAST"
  | ResoAST -> "ResoAST"
  | TautAST -> "TautAST"
  | ContAST -> "ContAST"
  | ReflAST -> "ReflAST"
  | TransAST -> "TransAST"
  | CongAST -> "CongAST"
  | EqreAST -> "EqreAST"
  | EqtrAST -> "EqtrAST"
  | EqcoAST -> "EqcoAST"
  | EqcpAST -> "EqcpAST"
  | AndAST -> "AndAST"
  | NorAST -> "NorAST"
  | OrAST -> "OrAST"
  | NandAST -> "NandAST"
  | Xor1AST -> "Xor1AST"
  | Xor2AST -> "Xor2AST"
  | Nxor1AST -> "Nxor1AST"
  | Nxor2AST -> "Nxor2AST"
  | ImpAST -> "ImpAST"
  | Nimp1AST -> "Nimp1AST"
  | Nimp2AST -> "Nimp2AST"
  | Equ1AST -> "Equ1AST"
  | Equ2AST -> "Equ2AST"
  | Nequ1AST -> "Nequ1AST"
  | Nequ2AST -> "Nequ2AST"
  | AndpAST -> "AndpAST"
  | AndnAST -> "AndnAST"
  | OrpAST -> "OrpAST"
  | OrnAST -> "OrnAST"
  | Xorp1AST -> "Xorp1AST"
  | Xorp2AST -> "Xorp2AST"
  | Xorn1AST -> "Xorn1AST"
  | Xorn2AST -> "Xorn2AST"
  | ImppAST -> "ImppAST"
  | Impn1AST -> "Impn1AST"
  | Impn2AST -> "Impn2AST"
  | Equp1AST -> "Equp1AST"
  | Equp2AST -> "Equp2AST"
  | Equn1AST -> "Equn1AST"
  | Equn2AST -> "Equn2AST"
  | Ite1AST -> "Ite1AST"
  | Ite2AST -> "Ite2AST"
  | Itep1AST -> "Itep1AST"
  | Itep2AST -> "Itep2AST"
  | Iten1AST -> "Iten1AST"
  | Iten2AST -> "Iten2AST"
  | Nite1AST -> "Nite1AST"
  | Nite2AST -> "Nite2AST"
  | ConndefAST -> "ConndefAST"
  | AndsimpAST -> "AndsimpAST"
  | OrsimpAST -> "OrsimpAST"
  | NotsimpAST -> "NotsimpAST"
  | ImpsimpAST -> "ImpsimpAST"
  | EqsimpAST -> "EqsimpAST"
  | BoolsimpAST -> "BoolsimpAST"
  | AcsimpAST -> "AcsimpAST"
  | ItesimpAST -> "ItesimpAST"
  | EqualsimpAST -> "EqualsimpAST"
  | DistelimAST -> "DistelimAST"
  | LageAST -> "LageAST"
  | LiageAST -> "LiageAST"
  | LataAST -> "LataAST"
  | LadeAST -> "LadeAST"
  | DivsimpAST -> "DivsimpAST"
  | ProdsimpAST -> "ProdsimpAST"
  | UminussimpAST -> "UminussimpAST"
  | MinussimpAST -> "MinussimpAST"
  | SumsimpAST -> "SumsimpAST"
  | CompsimpAST -> "CompsimpAST"
  | LarweqAST -> "LarweqAST"
  | BindAST -> "BindAST"
  | FinsAST -> "FinsAST"
  | QcnfAST -> "QcnfAST"
  | AllsimpAST -> "AllsimpAST"
  | SameAST -> "SameAST"
  | AnchorAST -> "AnchorAST"
  | DischargeAST -> "DischargeAST"
  | SubproofAST c -> "SubproofAST\n\t"^(string_of_certif c)^"\t"
and string_of_typ (t : typ) : string =
  match t with
  | Int -> "Int"
  | Bool -> "Bool"
  | Unintr s -> "(Unintr "^s^")"
and concat_sp x y = x^" "^y
and string_of_term (t : term) : string = 
  match t with
  | True -> "true"
  | False -> "false"
  | Not t -> "not ("^(string_of_term t)^")"
  | And ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "and ("^args^")"
  | Or ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "or ("^args^")"
  | Imp ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "imp ("^args^")"
  | Xor ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "xor ("^args^")"
  | Ite ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "ite ("^args^")"
  | Forall (xs, t) -> let args = List.fold_left concat_sp "" (List.map (fun (s,t) -> "(s : "^(string_of_typ t)^")") xs) in
      "forall ("^args^"), "^(string_of_term t)
  | Eq (t1, t2) -> (string_of_term t1)^" = "^(string_of_term t2)
  | App (f, ts) -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
                                f^" ("^args^")"
  | Var v -> v
  | STerm s -> s
  | NTerm (s, t) -> "("^(string_of_term t)^" :named "^s^")"
  | Int i -> string_of_int i
  | Lt (t1, t2) -> (string_of_term t1)^" < "^(string_of_term t2)
  | Leq (t1, t2) -> (string_of_term t1)^" <= "^(string_of_term t2)
  | Gt (t1, t2) -> (string_of_term t1)^" > "^(string_of_term t2)
  | Geq (t1, t2) -> (string_of_term t1)^" >= "^(string_of_term t2)
  | UMinus t -> "-"^(string_of_term t)
  | Plus (t1, t2) -> (string_of_term t1)^" + "^(string_of_term t2)
  | Minus (t1, t2) -> (string_of_term t1)^" - "^(string_of_term t2)
  | Mult (t1, t2) -> (string_of_term t1)^" * "^(string_of_term t2)
and string_of_clause (c : clause) =
  let args = List.fold_left concat_sp "" (List.map string_of_term c) in
  "(cl "^args^")"


(* Pass through certificate, replace named terms with their
   aliases, and store the alias-term mapping in a hash table *)

let sterms : (string, term) Hashtbl.t = Hashtbl.create 17
let get_sterm s =
  try Hashtbl.find sterms s
  with 
  | Not_found -> raise (Debug 
      ("| get_sterm : can't find "^s^" |"))
let add_sterm s t = Hashtbl.add sterms s t
let clear_sterms () = Hashtbl.clear sterms

(* Get expression modulo aliasing*)
let rec get_expr = function
  | STerm t -> 
      let t' = try get_sterm t with
               | Debug s -> 
                raise (Debug ("| get_expr: can't find sterm |")) in
      get_expr t'
  | NTerm (_, e) -> e
  | e -> e

let rec store_shared_terms_t (t : term) : term =
  match t with
  | True | False -> t
  | Not t' -> Not (store_shared_terms_t t')
  | And ts -> And (List.map store_shared_terms_t ts)
  | Or ts -> Or (List.map store_shared_terms_t ts)
  | Imp ts -> Imp (List.map store_shared_terms_t ts)
  | Xor ts -> Xor (List.map store_shared_terms_t ts)
  | Ite ts -> Ite (List.map store_shared_terms_t ts)
  | Forall (xs, t') -> Forall (xs, (store_shared_terms_t t'))
  | Eq (t1, t2) -> Eq ((store_shared_terms_t t1), (store_shared_terms_t t2))
  | App (f, ts) -> App (f, (List.map store_shared_terms_t ts))
  | Var s -> Var s
  | STerm s -> STerm s
  | NTerm (s, t') -> let t'' = store_shared_terms_t t' in
                     add_sterm s t''; STerm s
  | Int i -> Int i
  | Lt (t1, t2) -> Lt ((store_shared_terms_t t1), (store_shared_terms_t t2))
  | Leq (t1, t2) -> Leq ((store_shared_terms_t t1), (store_shared_terms_t t2))
  | Gt (t1, t2) -> Gt ((store_shared_terms_t t1), (store_shared_terms_t t2))
  | Geq (t1, t2) -> Geq ((store_shared_terms_t t1), (store_shared_terms_t t2))
  | UMinus t' -> UMinus (store_shared_terms_t t')
  | Plus (t1, t2) -> Plus ((store_shared_terms_t t1), (store_shared_terms_t t2))
  | Minus (t1, t2) -> Minus ((store_shared_terms_t t1), (store_shared_terms_t t2))
  | Mult (t1, t2) -> Mult ((store_shared_terms_t t1), (store_shared_terms_t t2))

let store_shared_terms_cl (c : clause) : clause =
  List.map store_shared_terms_t c

let rec store_shared_terms (c : certif) : certif = 
  match c with
  | (i, r, cl, p, a) :: t -> let cl' = (store_shared_terms_cl cl) in
                              (i, r, cl', p, a) :: store_shared_terms t
  | [] -> []



(* Term equality modulo alpha renaming of foralls *)

let type_eq (t1 : typ) (t2 : typ) : bool =
  match t1, t2 with
  | Int, Int -> true
  | Bool, Bool -> true
  | Unintr s1, Unintr s2 -> s1 = s2
  | _, _ -> false

let rec term_eq_alpha (subs : (string * string) list) (t1 : term) (t2 : term) : bool =
  let t1 = get_expr t1 in
  let t2 = get_expr t2 in
  let check_arg_lists (x : term list) (y : term list) : bool =
    if List.length x = List.length y then
      List.fold_left (&&) true (List.map2 (term_eq_alpha subs) x y)
    else false
  in match t1, t2 with
  | True, True -> true
  | False, False -> true
  | Not t1', Not t2' -> term_eq_alpha subs t1' t2'
  | And ts1, And ts2 -> check_arg_lists ts1 ts2
  | Or ts1, Or ts2 -> check_arg_lists ts1 ts2
  | Imp ts1, Imp ts2 -> check_arg_lists ts1 ts2
  | Xor ts1, Xor ts2 -> check_arg_lists ts1 ts2
  | Ite ts1, Ite ts2 -> check_arg_lists ts1 ts2
  | Forall (xs, t1'), Forall (ys, t2') ->
      raise (Debug ("| term_eq_alpha: checking equality of forall inside forall |"))
  | Eq (t11, t12), Eq (t21, t22) -> term_eq_alpha subs t11 t21 && term_eq_alpha subs t12 t22
  | App (f1, t1'), App (f2, t2') -> f1 = f2 && check_arg_lists t1' t2'
  | Var x, Var y -> x = y || 
    List.exists (fun (a, b) -> a = x && b = y || a = y && b = x) subs
  | STerm x, STerm y -> x = y
  | NTerm (s1, t1'), NTerm (s2, t2') -> s1 = s2 && term_eq_alpha subs t1' t2'
  | Int i, Int j -> i = j
  | Lt (t11, t12), Lt (t21, t22) -> term_eq_alpha subs t11 t21 && term_eq_alpha subs t12 t22
  | Leq (t11, t12), Leq (t21, t22) -> term_eq_alpha subs t11 t21 && term_eq_alpha subs t12 t22
  | Gt (t11, t12), Gt (t21, t22) -> term_eq_alpha subs t11 t21 && term_eq_alpha subs t12 t22
  | Geq (t11, t12), Geq (t21, t22) -> term_eq_alpha subs t11 t21 && term_eq_alpha subs t12 t22
  | UMinus t1', UMinus t2' -> term_eq_alpha subs t1' t2'
  | Plus (t11, t12), Plus (t21, t22) -> term_eq_alpha subs t11 t21 && term_eq_alpha subs t12 t22
  | Minus (t11, t12), Minus (t21, t22) -> term_eq_alpha subs t11 t21 && term_eq_alpha subs t12 t22
  | Mult (t11, t12), Mult (t21, t22) -> term_eq_alpha subs t11 t21 && term_eq_alpha subs t12 t22
  | _ -> false

let rec term_eq (t1 : term) (t2 : term) : bool =
  let t1 = get_expr t1 in
  let t2 = get_expr t2 in
  let check_arg_lists (x : term list) (y : term list) : bool =
    if List.length x = List.length y then
      List.fold_left (&&) true (List.map2 term_eq x y)
    else false
  in match t1, t2 with
  | True, True -> true
  | False, False -> true
  | Not t1', Not t2' -> term_eq t1' t2'
  | And ts1, And ts2 -> check_arg_lists ts1 ts2
  | Or ts1, Or ts2 -> check_arg_lists ts1 ts2
  | Imp ts1, Imp ts2 -> check_arg_lists ts1 ts2
  | Xor ts1, Xor ts2 -> check_arg_lists ts1 ts2
  | Ite ts1, Ite ts2 -> check_arg_lists ts1 ts2
  | Forall (xs, t1'), Forall (ys, t2') ->
      let subs = List.map2 (fun (x, tx) (y, ty) -> (x, y)) xs ys in
      (List.length xs = List.length ys) &&
      (List.fold_left (&&) true 
        (List.map2 (fun (x, tx) (y, ty) -> type_eq tx ty) xs ys)) && 
      term_eq_alpha subs t1' t2'
  | Eq (t11, t12), Eq (t21, t22) -> term_eq t11 t21 && term_eq t12 t22
  | App (f1, t1'), App (f2, t2') -> f1 = f2 && check_arg_lists t1' t2'
  | Var x, Var y -> x = y
  | STerm x, STerm y -> x = y
  | NTerm (s1, t1'), NTerm (s2, t2') -> s1 = s2 && term_eq t1' t2'
  | Int i, Int j -> i = j
  | Lt (t11, t12), Lt (t21, t22) -> term_eq t11 t21 && term_eq t12 t22
  | Leq (t11, t12), Leq (t21, t22) -> term_eq t11 t21 && term_eq t12 t22
  | Gt (t11, t12), Gt (t21, t22) -> term_eq t11 t21 && term_eq t12 t22
  | Geq (t11, t12), Geq (t21, t22) -> term_eq t11 t21 && term_eq t12 t22
  | UMinus t1', UMinus t2' -> term_eq t1' t2'
  | Plus (t11, t12), Plus (t21, t22) -> term_eq t11 t21 && term_eq t12 t22
  | Minus (t11, t12), Minus (t21, t22) -> term_eq t11 t21 && term_eq t12 t22
  | Mult (t11, t12), Mult (t21, t22) -> term_eq t11 t21 && term_eq t12 t22
  | _ -> false


(* Process forall_inst rule by:
   1. Ignoring all alpha renaming sub-proofs 
   2. Dealing with the qnt_cnf rule 
   3. Finding the lemma from the inputs and passing it as a premise
      to forall_inst 
      Replacing the clause in the forall_inst rule by its instance *)

(* Returns the id of the assumption in c which is identical to t *)
let rec find_lemma (t : term) (c : certif) : id =
  match c with
  | (i, r, cl, p, a) :: tl ->
      (match r, cl with
      | AssumeAST, (t' :: _) when term_eq t t' -> i
      | _ -> find_lemma t tl)
  | [] -> raise (Debug ("| find_lemma: can't find lemma to be instantiated by forall_inst |"))

(* Remove all occurrences of element from list *)
let rec remove x l =
  match l with
  | h :: t -> if h = x then remove x t else h :: (remove x t)
  | [] -> []

(* Remove premise from all resolutions in certif *)
let rec remove_res_premise (i : id) (c : certif) : certif =
  match c with
  | (i', r, c, p, a) :: t -> 
      (match r with
      | ResoAST | ThresoAST -> (i', r, c, (remove i p), a) :: (remove_res_premise i t)
      | _ -> (i', r, c, p, a) :: (remove_res_premise i t))
  | [] -> []

let process_fins (c : certif) : certif =
  let rec process_fins_aux (c : certif) (cog : certif) : certif =
    match c with
    (* Step 1 *)
    | (i1, AnchorAST, c1, p1, a1) :: (i2, ReflAST, c2, p2, a2) ::
      (i3, CongAST, c3, p3, a3)   :: (i4, BindAST, c4, p4, a4) ::
      (i5, Equp2AST, c5, p5, a5)  :: (i6, ThresoAST, c6, p6, a6) :: t ->
        process_fins_aux (remove_res_premise i6 t) cog
    (* Step 2 *)
    | (_, QcnfAST, c, _, _) :: t ->
        (* Ignoring this rule assuming no transformation is performed, 
           we need to handle this rule for more complex CNF 
           transformations of quantified formulas*)
        process_fins_aux t cog
    (* Step 3 *)
    | (i, FinsAST, c, p, a) :: tl -> 
        let st = (match (List.hd c) with
        | Or [e; t2] ->
          let t = get_expr e in
            (match t with
            | Not t -> 
                let lem = try find_lemma t cog with 
                  | Debug s -> raise 
                    (Debug ("| process_fins: failing at id "^i^" |"^s)) in
                (i, FinsAST, [t2], [lem], [])
            | _ -> raise (Debug 
                ("| process_fins: arg of forall_inst expected to be (or (Not lemma) instance) at "
                 ^i^" |")))
        | _ -> raise (Debug 
               ("| process_fins: arg of forall_inst expected to be an `or` at "
                ^i^" |")))
        in st :: process_fins_aux tl cog
    | ircpa :: t -> ircpa :: process_fins_aux t cog
    | [] -> []
  in process_fins_aux c c



(* Remove notnot rule from certificate *)

(* Soundly remove all notnot rules from certificate *)
let rec remove_notnot (c : certif) : certif = 
  match c with
  | (i, r, cl, p, a) :: t ->
      (match r with
      | NotnotAST -> remove_notnot (remove_res_premise i t)
      | _ -> (i, r, cl, p, a) :: remove_notnot t)
  | [] -> []



(* Convert an AST to a list of clauses *)

let process_typ (t : typ) : SmtBtype.btype =
  match t with
  | Int -> TZ
  | Bool -> Tbool
  | Unintr _ -> assert false (* needs to be updated *)

let rec process_vars (vs : (string * typ) list) : (string * SmtBtype.btype) list = 
  match vs with
  | (s, t) :: tl -> let t' = process_typ t in
                    add_qvar s t'; (s, t') :: process_vars tl
  | [] -> []

let rec process_term (x: bool * SmtAtom.Form.atom_form_lit) : SmtAtom.Form.t =
  Form.lit_of_atom_form_lit rf x

(*term |-> bool * SmtAtom.Form.atom_form_lit |-> SmtAtom.Form.t*)

and process_term_aux (t : term) : bool * SmtAtom.Form.atom_form_lit (*option*) =
  let process (t : term) : (bool * SmtAtom.Form.t) =
    let decl, t' = process_term_aux t in
    let t'' = process_term (decl, t') in
    decl, t''
  in match t with
  | True -> true, Form.Form Form.pform_true
  | False -> true, Form.Form Form.pform_false
  | Not t -> let decl, t' = process t in 
             decl, Form.Lit (Form.neg t')
  | And ts -> apply_dec (fun x -> Form.Form (Fapp (Fand, Array.of_list x)))
              (list_dec (List.map process ts))
  | Or ts ->  apply_dec (fun x -> Form.Form (Fapp (For, Array.of_list x)))
              (list_dec (List.map process ts))
  | Imp ts -> apply_dec (fun x -> Form.Form (Fapp (Fimp, Array.of_list x)))
              (list_dec (List.map process ts))
  | Xor ts -> apply_dec (fun x -> Form.Form (Fapp (Fxor, Array.of_list x)))
              (list_dec (List.map process ts))
  | Ite ts -> apply_dec (fun x -> Form.Form (Fapp (Fite, Array.of_list x)))
              (list_dec (List.map process ts))
  | Forall (vs, t) -> let vs' = process_vars vs in
                      let decl, t' = process t in
                      clear_qvar ();
                      false, Form.Form (Fapp (Fforall vs', [|t'|]))
  | Eq (t1, t2) -> 
      (match (process_term_aux t1), (process_term_aux t2) with 
      | (decl1, Form.Atom h1), (decl2, Form.Atom h2) when (match Atom.type_of h1 with 
                                                           | SmtBtype.Tbool -> false 
                                                           | _ -> true)
            -> let decl = decl1 && decl2 in decl, Form.Atom (Atom.mk_eq_sym ra ~declare:decl 
                                         (Atom.type_of h1) h1 h2) 
      | (decl1, t1), (decl2, t2) -> 
               decl1 && decl2, Form.Form (Fapp (Fiff, 
                                    [|Form.lit_of_atom_form_lit rf (decl1, t1); 
                                      Form.lit_of_atom_form_lit rf (decl2, t2)|])))
  | App (f, ts) -> let ts' = List.map process_term_aux ts in
                   let args = List.map (fun x -> match x with 
                               | decl, Form.Atom h -> (decl, h)
                               | _ -> assert false) ts' in
      (match find_opt_qvar f with
      | Some bt -> let op = dummy_indexed_op (Rel_name f) [||] bt in
                   false, Form.Atom (Atom.get ~declare:false ra (Aapp (op, Array.of_list (snd (list_dec args))))) 
      | None ->    let dl, l = list_dec args in 
                   dl, Form.Atom (Atom.get ra ~declare:dl (Aapp (SmtMaps.get_fun f, Array.of_list l))))
  | Var s -> (match find_opt_qvar s with
             | Some bt   -> false, 
                Form.Atom (Atom.get ~declare:false ra (Aapp (dummy_indexed_op (Rel_name s) [||] bt, [||])))
             | None      -> true, Form.Atom (Atom.get ra (Aapp (SmtMaps.get_fun s, [||]))))
  | STerm s ->
      (* s has either been processed and stored in the solver hashtable, 
         or it has to be fetched first from the sterms hashtable, processed,
         stored in the solver hashtable and then returned *)
      (try get_solver s with
       | Debug _ -> let t' = (try get_sterm s with
                              | Debug d -> raise (Debug 
                                ("| process_term_aux: can't find "^s^" |"^d))) in
                    let t'' = process_term_aux t' in
                              add_solver s t''; t'')
  | NTerm (s, t) -> let t' = process_term_aux t in
                    add_solver s t'; t'
  | Int i -> true, Form.Atom (Atom.hatom_Z_of_int ra i)
  | Lt (x,y) -> let x' = process_term_aux x in
                let y' = process_term_aux y in 
                apply_bdec_atom (Atom.mk_lt ra) x' y'
  | Leq (x,y) -> let x' = process_term_aux x in
                 let y' = process_term_aux y in 
                 apply_bdec_atom (Atom.mk_le ra) x' y'
  | Gt (x,y) -> let x' = process_term_aux x in
                let y' = process_term_aux y in 
                apply_bdec_atom (Atom.mk_gt ra) x' y'
  | Geq (x,y) -> let x' = process_term_aux x in
                 let y' = process_term_aux y in 
                 apply_bdec_atom (Atom.mk_ge ra) x' y'
  | UMinus t -> let t' = process_term_aux t in
                apply_dec_atom (fun ?declare:d a -> Atom.mk_neg ra a) t'
  | Plus (x,y) -> let x' = process_term_aux x in
                  let y' = process_term_aux y in 
                  apply_bdec_atom (Atom.mk_plus ra) x' y'
  | Minus (x,y) -> let x' = process_term_aux x in
                   let y' = process_term_aux y in
                   apply_bdec_atom (Atom.mk_minus ra) x' y'
  | Mult (x,y) -> let x' = process_term_aux x in
                  let y' = process_term_aux y in
                  apply_bdec_atom (Atom.mk_mult ra) x' y'

let process_cl (c : clause) : SmtAtom.Form.t list =
  List.map (fun x -> process_term (process_term_aux x)) c

let process_rule (r: rule) : VeritSyntax.typ =
  match r with
  | AssumeAST -> Assume
  | TrueAST -> True
  | FalsAST -> Fals
  | NotnotAST -> Notnot
  | ThresoAST -> Threso
  | ResoAST -> Reso
  | TautAST -> Taut
  | ContAST -> Cont
  | ReflAST -> Refl
  | TransAST -> Trans
  | CongAST -> Cong
  | EqreAST -> Eqre
  | EqtrAST -> Eqtr
  | EqcoAST -> Eqco
  | EqcpAST -> Eqcp
  | AndAST -> And
  | NorAST -> Nor
  | OrAST -> Or
  | NandAST -> Nand
  | Xor1AST -> Xor1 
  | Xor2AST -> Xor2
  | Nxor1AST -> Nxor1 
  | Nxor2AST -> Nxor2
  | ImpAST -> Imp
  | Nimp1AST -> Nimp1
  | Nimp2AST -> Nimp2
  | Equ1AST -> Equ1
  | Equ2AST -> Equ2
  | Nequ1AST -> Nequ1
  | Nequ2AST -> Nequ2
  | AndpAST -> Andp
  | AndnAST -> Andn
  | OrpAST -> Orp
  | OrnAST -> Orn
  | Xorp1AST -> Xorp1
  | Xorp2AST -> Xorp2
  | Xorn1AST -> Xorn1
  | Xorn2AST -> Xorn2
  | ImppAST -> Impp
  | Impn1AST -> Impn1
  | Impn2AST -> Impn2
  | Equp1AST -> Equp1
  | Equp2AST -> Equp2
  | Equn1AST -> Equn1
  | Equn2AST -> Equn2
  | Ite1AST -> Ite1
  | Ite2AST -> Ite2
  | Itep1AST -> Itep1
  | Itep2AST -> Itep2
  | Iten1AST -> Iten1
  | Iten2AST -> Iten2
  | Nite1AST -> Nite1
  | Nite2AST -> Nite2
  | ConndefAST -> Conndef
  | AndsimpAST -> Andsimp
  | OrsimpAST -> Orsimp
  | NotsimpAST -> Notsimp
  | ImpsimpAST -> Impsimp
  | EqsimpAST -> Eqsimp
  | BoolsimpAST -> Boolsimp
  | AcsimpAST -> Acsimp
  | ItesimpAST -> Itesimp
  | EqualsimpAST -> Equalsimp
  | DistelimAST -> Distelim
  | LageAST -> Lage
  | LiageAST -> Liage
  | LataAST -> Lata
  | LadeAST -> Lade
  | DivsimpAST -> Divsimp
  | ProdsimpAST -> Prodsimp
  | UminussimpAST -> Uminussimp
  | MinussimpAST -> Minussimp
  | SumsimpAST -> Sumsimp
  | CompsimpAST -> Compsimp
  | LarweqAST -> Larweq
  | BindAST -> Bind
  | FinsAST -> Fins
  | QcnfAST -> Qcnf
  | AllsimpAST -> Allsimp
  | SameAST -> Same
  | AnchorAST -> Hole
  | DischargeAST -> Hole
  | SubproofAST c -> Hole



(* Removing occurrences of the cong rule using other rules 
   including eq_congruent, eq_congruent_pred, reso *)

(* We use eq_congruent_pred to prove cong (in the predicate case). 
   It is an elaborate process, but it saves us the effort of 
   proving a new rule correct. For cong, we have
   x1 = y1 and x2 = y2, and we need to prove Px = Py, 
      short for P(x1, x2) = P(y1, y2)
   ~(x1 = y1) \/ ~(x2 = y2) \/ ~Px \/ Py --(1) by eq_congruent_pred
   ~(x1 = y1) \/ ~(x2 = y2) \/ ~Py \/ Px --(2) by eq_congruent_pred
   (1)  (x1 = y1)  (x2 = y2)        (2)  (x1 = y1)  (x2 = y2)
   -------------------------Res     -------------------------Res
        ~Px \/ Py --(3)                   ~Py \/ Px --(4)
  
  Px = Py \/ Px \/ Py   --(5) by equiv_neg2
  Px = Py \/ ~Px \/ ~Py --(6) by equiv_neg1
  Finally,
    (3)  (5)          (4)  (6)
  -------------Res  --------------Res
  Px = Py \/ Py      Px = Py \/ ~Py
  ---------------------------------Res
               Px = Py
  We do something similar for the function case of cong, except 
  that there is 1 intermediate step of calling eq_congruent, 
  followed by a resolution. Here, there are 8. Because, when 
  the intermediate step numbers are generated in VeritAst, 
  it is not possible to determine the case of cong, VeritAst
  passes 8 clause IDs to the cong rule as args (in Alethe, the
  cong rule has no args)
*)
(*
  TODO: Predicate case. Issues: Currently all premises are expected to explicit,
  but the rule uses implicit premises such as true = true, which need to be 
  inferred and added to the resolutions (for each of these premises a rule of refl
  must be invoked). Without this, process_congr_form probably fails.
*)
let process_cong (c : certif) : certif = 
  let rec process_cong_aux (c : certif) (cog : certif) : certif = 
    match c with
    | (i, r, c, p, a) :: t ->
        (match r with
        | CongAST ->
            let c' = process_cl c in
            (match c' with
            | l::_ ->
                (* get premises and convert from clauses to formulas *)
                let prems = List.map (fun x -> (match (get_cl x cog) with
                | Some x -> Not (List.hd x)
                | None -> raise (Debug ("| process_cong: can't fetch premises to congr at id "^i)))) p in
                (* congruence over functions *)
                if is_eq l then
                  let new_id = VeritSyntax.generate_id () in
                  (* perform application of eq_congruent to 
                   get a CNF form of the rule application *)
                  let new_cl = mk_cl (prems @ c) in
                  (* then, resolve out all the premises from the CNF so only 
                   the conclusion is left *)
                  (new_id, EqcoAST, new_cl, [], []) ::
                  (i, ResoAST, c, new_id :: p, a) :: process_cong_aux t cog
                (* congruence over predicates*)
                (*else if is_iff l then
                  let new_id1 = VeritSyntax.generate_id () in
                  let new_id2 = VeritSyntax.generate_id () in
                  let new_id3 = VeritSyntax.generate_id () in
                  let new_id4 = VeritSyntax.generate_id () in
                  let new_id5 = VeritSyntax.generate_id () in
                  let new_id6 = VeritSyntax.generate_id () in
                  let new_id7 = VeritSyntax.generate_id () in
                  let new_id8 = VeritSyntax.generate_id () in
                  let (c1, c2) = (match List.hd c with
                                  | Eq (x, y) -> (x, y)
                                  | _ -> assert false) in
                  (* Construct (1) and (2) *)
                  let cl1 = (new_id1, EqcpAST, mk_cl (prems @ [Not c1] @ [c2]), [], []) in
                  let cl2 = (new_id2, EqcpAST, mk_cl (prems @ [Not c2] @ [c1]), [], []) in
                  (* Construct (3) and (4) *)
                  let cl3 = (new_id3, ResoAST, mk_cl [Not c1; c2], new_id1::p, []) in
                  let cl4 = (new_id4, ResoAST, mk_cl [Not c2; c1], new_id2::p, []) in
                  (* Construct (5) and (6) *)
                  let cl5 = (new_id5, Nequ2AST, mk_cl [List.hd c; c1; c2], [], []) in
                  let cl6 = (new_id6, Nequ1AST, mk_cl [List.hd c; Not c1; Not c2], [], []) in
                  (* Final resolutions *)
                  let cl7 = (new_id7, ResoAST, mk_cl [List.hd c; c1], [new_id3; new_id5], []) in
                  let cl8 = (new_id8, ResoAST, mk_cl [List.hd c; Not c1], [new_id4; new_id6], []) in
                  let cl9 = (i, ResoAST, c, [new_id7; new_id8], []) in
                  cl1 :: cl2 :: cl3 :: cl4 :: cl5 :: cl6 :: cl7 :: cl8 :: cl9 :: process_cong_aux t cog*)
                else
                  (i, r, c, p, a) :: process_cong_aux t cog
              | _ -> assert false)
        | _ -> (* This is necessary to add the shared terms to the hash tables *)
               let _ = process_cl c in
               (i, r, c, p, a) :: process_cong_aux t cog)
    | [] -> []
    in process_cong_aux c c


(* SMTCoq requires projection rules `and`, `not_or`, `or_neg`, `and_pos`
   to specify an integer argument specifying the term to project.
   Alethe doesn't specify the projection for these rules. This 
   transformation searches the clause for the projection and adds
   it as an argument *)

(* list_find_index l x eq returns the index of the 
   first occurrence of item x in list l, using eq for 
   item equality checking *)
let list_find_index l x eq : int =
  let rec aux i l = 
    match l with
    | h :: t -> if eq h x then i else aux (i+1) t
    | [] -> raise (Debug "| list_find_index: failed |")
  in aux 0 l

let process_proj (c: certif): certif =
  let rec aux (c: certif) (cog: certif) : certif =
    match c with
    | (i, AndAST, cl, p, a) :: tl ->
        let p' = List.map (fun x -> match get_cl x cog with
                           | Some x' -> List.hd x'
                           | None -> raise (Debug ("Can't fetch premises to `and` at id "
                                            ^i^" |"))) 
                 p in
        (match (get_expr (List.hd p')), (get_expr (List.hd cl)) with
        | And ts, x ->
            let i' = try list_find_index ts x term_eq with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "
                        ^i^" |"^s)) in
              (i, AndAST, cl, p, [(string_of_int i')]) :: aux tl cog
        | _, _ -> raise (Debug ("| process_proj: expecting premise to be an `and` at id "
                         ^i^" |")))
    | (i, NorAST, cl, p, a) :: tl ->
        let p' = List.map (fun x -> match get_cl x cog with
                           | Some x' -> List.hd x'
                           | None -> raise (Debug 
                              ("| process_proj: can't fetch premises to `and` at id "
                              ^i^" |")))
                 p in
        (match (get_expr (List.hd p')), (get_expr (List.hd cl)) with
        | Not (Or ts), Not x -> 
            let i' = try list_find_index ts x term_eq with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "^i^" |"^s)) in
              (i, AndAST, cl, p, [(string_of_int i')]) :: aux tl cog
        | _, _ -> raise (Debug ("| process_proj: expecting premise to be a `not (or)` at id "
                  ^i^" |")))
    | (i, OrnAST, cl, p, a) :: tl ->
        (match get_expr (List.nth cl 0), get_expr (List.nth cl 1) with
        | Or ts, Not x -> 
            let i' = try list_find_index ts x term_eq with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "^i^" |"^s)) in
              (i, AndAST, cl, p, [(string_of_int i')]) :: aux tl cog
        | _, _ -> raise (Debug 
                  ("| process_proj: expecting clause with `or` and `not` at id "^i^" |")))
    | (i, AndpAST, cl, p, a) :: tl ->
        (match get_expr (List.nth cl 0), get_expr (List.nth cl 1) with
        | Not (And ts), x ->
            let i' = try list_find_index ts x term_eq with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "^i^" |"^s)) in
              (i, AndAST, cl, p, [(string_of_int i')]) :: aux tl cog
        |  _, _ -> raise (Debug ("| process_proj: expecting clause with `not (and)` and projection at id "
                   ^i^" |")))
    | ircpa :: tl -> ircpa :: (aux tl cog)
    | [] -> []
  in aux c c


(* Flatten subproofs *)
(* TODO: Don't forget to flatten subproofs within subproofs!!! *)

(* Function that takes a certif, a list of id pairs, and 
   performs id substitution in the certif *)
let rec subst_id (c : certif) (subst : id * id) : certif =
  match c, subst with
  | (i1, r, cl, p, a) :: tl, (i2, i3) ->
      if i1 = i2 then (i3, r, cl, p, a) :: subst_id tl subst
      else (i1, r, cl, p, a) :: subst_id tl subst
  | [], _ -> []
let rec subst_ids (c : certif) (subst : (id * id) list) : certif =
  match subst with
  | h :: t -> subst_ids (subst_id c h) t
  | [] -> c

let process_subproof_aux (i : id) (hd_id : id) (h : term) (g : term) (subp : certif) (c : certif) : certif =
  match c with
  | (i', ResoAST, cl', p', a') :: tl when (List.exists (fun x -> x = i) p') ->
    let res1 = match List.hd (List.rev subp) with
               | (i, _, _, _, _) -> i in
    let res2 = generate_id () in
      (i', ResoAST, (And (h :: (Not g) :: [])) :: [], p', a') ::
      ((generate_id ()), AndAST, h :: [], [i'], []) ::
      (subp @ tl @ 
       [(res2, AndAST, Not g :: [], [i'], []);
        ((generate_id ()), ResoAST, [], [res1;res2], [])]) 
  | x -> x

let rec process_subproof (c : certif) : certif =
  match c with
  | (i, SubproofAST cert, cl, p, a) :: tl ->
      (match List.hd (List.rev cert) with
      | (i', DischargeAST, (Not h) :: g :: [], p', a') ->
        (* Remove first and last element of sub-proof certificate *)
        let certtl = List.tl cert in
        let subp = List.rev (List.tl (List.rev certtl)) in
        (* The assumption of the subproof will be derived in a new rule,
           we need to replace all calls to it with calls to the replaced
           rule *)
        let hd_id = match (List.hd cert) with
                   | (i, _, _, _, _) -> i in
        let new_id = generate_id () in
        let subp' = subst_ids subp ((hd_id, new_id) :: []) in
        (* (h ^ ~g) v ~h v g *)
        let t' = (And (h :: Not g :: [])) :: Not h :: g :: [] in
        (i', AndnAST, Or t' :: [], [], []) ::
        ((generate_id ()), OrAST, t', [i'], []) ::
        (process_subproof (process_subproof_aux i' new_id h g subp' tl))
      | _ -> raise (Debug ("| process_subproof: expecting a discharge step at id "^i^" |")))
  | (i, r, cl, p, a) :: tl -> (i, r, cl, p, a) :: process_subproof tl
  | [] -> []


(* Final processing and linking of AST *)

let preprocess_certif (c: certif) : certif =
  Printf.printf ("Certif before preprocessing: %s\n") (string_of_certif c);
  try 
  (let c1 = store_shared_terms c in
  Printf.printf ("Certif after storing shared terms: %s\n") (string_of_certif c1);
  let c2 = remove_notnot c1 in
  Printf.printf ("Certif after remove_notnot: %s\n") (string_of_certif c2);
  let c3 = process_fins c2 in
  Printf.printf ("Certif after process_fins: %s\n") (string_of_certif c3);
  let c4 = process_cong c3 in
  Printf.printf ("Certif after process_cong: %s\n") (string_of_certif c4);
  let c5 = process_proj c4 in
  Printf.printf ("Certif after process_proj: %s\n") (string_of_certif c5);
  c5) with
  | Debug s -> raise (Debug ("| VeritAst.preprocess_certif: failed to preprocess |"^s))

let rec process_certif (c : certif) : VeritSyntax.id list =
  match c with
  | (i, r, c, p, a) :: t ->
      let i' = VeritSyntax.id_of_string i in
      let r' = process_rule r in
      let c' = try process_cl c with
               | Debug s -> raise (Debug 
                  ("| VeritAst.process_certif: can't process clause at id "
                  ^i^" |")) in
      let p' = List.map (VeritSyntax.id_of_string) p in
      let a' = List.map (VeritSyntax.id_of_string) a in
      (* Must do this in this order to avoid side effects *)
      let res = mk_clause (i', r', c', p', a') in
      (* Process next step for linking *)
      let t' = process_certif t in
      if List.length t' > 0 then (
        let x = List.hd t' in
        try SmtTrace.link (get_clause res) (get_clause x) with
        | Debug s -> raise (Debug ("| VeritAst.process_certif: linking clauses |"^s))
        ) else ();
      res :: t'
  | [] -> []