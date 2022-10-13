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

let get_id (s : step) : id =
  match s with
  | (i, _, _, _, _) -> i

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
  | True -> "(true)"
  | False -> "(false)"
  | Not t -> "(not "^(string_of_term t)^")"
  | And ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "(and "^args^")"
  | Or ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "(or "^args^")"
  | Imp ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "(imp "^args^")"
  | Xor ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "(xor "^args^")"
  | Ite ts -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
      "(ite "^args^")"
  | Forall (xs, t) -> let args = List.fold_left concat_sp "" (List.map (fun (s,t) -> "(s : "^(string_of_typ t)^")") xs) in
      "(forall "^args^", "^(string_of_term t)^")"
  | Eq (t1, t2) -> "("^(string_of_term t1)^" = "^(string_of_term t2)^")"
  | App (f, ts) -> let args = List.fold_left concat_sp "" (List.map string_of_term ts) in
                                "("^f^" ("^args^"))"
  | Var v -> v
  | STerm s -> s
  | NTerm (s, t) -> "("^(string_of_term t)^" :named "^s^")"
  | Int i -> string_of_int i
  | Lt (t1, t2) -> "("^(string_of_term t1)^" < "^(string_of_term t2)^")"
  | Leq (t1, t2) -> "("^(string_of_term t1)^" <= "^(string_of_term t2)^")"
  | Gt (t1, t2) -> "("^(string_of_term t1)^" > "^(string_of_term t2)^")"
  | Geq (t1, t2) -> "("^(string_of_term t1)^" >= "^(string_of_term t2)^")"
  | UMinus t -> "("^"-"^(string_of_term t)^")"
  | Plus (t1, t2) -> "("^(string_of_term t1)^" + "^(string_of_term t2)^")"
  | Minus (t1, t2) -> "("^(string_of_term t1)^" - "^(string_of_term t2)^")"
  | Mult (t1, t2) -> "("^(string_of_term t1)^" * "^(string_of_term t2)^")"
and string_of_clause (c : clause) =
  let args = List.fold_left concat_sp "" (List.map (fun x -> "("^string_of_term x^")") c) in
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

let remove (x : 'a) (l : 'a list) = 
  List.fold_left (fun acc t -> if x = t then acc else t :: acc) [] l
(* Remove premise from all resolutions in certif *)
let remove_res_premise (i : id) (c : certif) : certif =
  List.map (fun s -> match s with
               | (i', r, c, p, a) when (r = ResoAST || r = ThresoAST) ->
                    (i', r, c, (remove i p), a)
               | s -> s) c

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
(* We assume that a ~~x is stored as just x by process_term *)
(* So typically, a proof that eliminates ~~ by:
     ...
   -------   ---------not_not
   ~~x v C    ~~~x v x
  --------------------reso
         x v C
  can be replaced by the following, since double negations 
  are implicitly simplified at the term level
    ...
   -------
    x v C
  --------reso
    x v C
*)
let rec process_notnot (c : certif) : certif = 
  match c with
  | (i, NotnotAST, cl, p, a) :: tl -> process_notnot (remove_res_premise i tl)
  | (i, NotsimpAST, [Eq (Not (Not x), y)], p, a) :: tl when x = y -> 
      (i, ReflAST, [Eq (x, x)], [], []) :: process_notnot tl
  | h :: tl -> h :: process_notnot tl
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
  TODO: Predicate case. Issues: Currently all premises are expected to be explicit,
  but the rule uses implicit premises such as true = true, which need to be 
  inferred and added to the resolutions (for each of these premises a rule of refl
  must be invoked). Without this, process_congr_form will probably fail.
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

(* findi x l 0 finds the index of x in l counting from 0 
   Note that it checks for syntactic equality of terms, not modulo
   alpha renaming *)
let findi (x : 'a) (l : 'a list) : int = 
  let rec findi' (x : 'a) (l : 'a list) (n : int) : int = 
    match l with
    | h :: t -> if h = x then n else findi' x t (n+1)
    | [] -> raise (Debug ("| findi : element not found |")) in
  findi' x l 0

let process_proj (c: certif): certif =
  let rec aux (c: certif) (cog: certif) : certif =
    match c with
    | (i, AndAST, cl, p, a) :: tl when a = [] ->
        let p' = List.map (fun x -> match get_cl x cog with
                           | Some x' -> List.hd x'
                           | None -> raise (Debug ("Can't fetch premises to `and` at id "
                                            ^i^" |"))) 
                 p in
        (match (get_expr (List.hd p')), (get_expr (List.hd cl)) with
        | And ts, x ->
            let i' = try findi x ts with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "
                        ^i^" |"^s)) in
              (i, AndAST, cl, p, [(string_of_int i')]) :: aux tl cog
        | _, _ -> raise (Debug ("| process_proj: expecting premise to be an `and` at id "
                         ^i^" |")))
    | (i, NorAST, cl, p, a) :: tl when a = [] ->
        let p' = List.map (fun x -> match get_cl x cog with
                           | Some x' -> List.hd x'
                           | None -> raise (Debug 
                              ("| process_proj: can't fetch premises to `and` at id "
                              ^i^" |")))
                 p in
        (match (get_expr (List.hd p')), (get_expr (List.hd cl)) with
        | Not (Or ts), Not x -> 
            let i' = try findi x ts with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "^i^" |"^s)) in
              (i, NorAST, cl, p, [(string_of_int i')]) :: aux tl cog
        | _, _ -> raise (Debug ("| process_proj: expecting premise to be a `not (or)` at id "
                  ^i^" |")))
    | (i, OrnAST, cl, p, a) :: tl when a = [] ->
        (match get_expr (List.nth cl 0), get_expr (List.nth cl 1) with
        | Or ts, Not x -> 
            let i' = try findi x ts with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "^i^" |"^s)) in
              (i, OrnAST, cl, p, [(string_of_int i')]) :: aux tl cog
        | _, _ -> raise (Debug 
                  ("| process_proj: expecting clause with `or` and `not` at id "^i^" |")))
    | (i, AndpAST, cl, p, a) :: tl when a = [] ->
        (match get_expr (List.nth cl 0), get_expr (List.nth cl 1) with
        | Not (And ts), x ->
            let i' = try findi x ts with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "^i^" |"^s)) in
              (i, AndpAST, cl, p, [(string_of_int i')]) :: aux tl cog
        |  _, _ -> raise (Debug ("| process_proj: expecting clause with `not (and)` and projection at id "
                   ^i^" |")))
    | ircpa :: tl -> ircpa :: (aux tl cog)
    | [] -> []
  in aux c c


(* Flatten subproofs *)
(* TODO: Add projection arguments in the flattening, so the projections transformation
   can be done before this one *)
(* TODO: Don't forget to flatten subproofs within subproofs!!! *)
(*
  Pi_1                                         Pi_1
...                                     ...
--------                                -----------------and_neg
| [H]  |                                [(H ^ ~G), ~H, G]               --(2)
| Pi_2 |                                ...       
|  G   |                                Pi_3'
--------               ----->           ...        
 [~H, G] --(1)                          H ^ ~G                          --(3)
...                                     --------and'
  Pi_3                                      H --(4)         H ^ ~G      --(3)      
...                                        Pi_2             ------and'        
   []                                       G                 ~G        --(5)
                                            --------------------
                                                     []                 --(6)               
Pi_3' replaces every step in Pi_3 that directly or indirectly uses (1), so that the result 
naturally produces the original result v (H ^ ~G) 

and' is and implemented through andPos and reso
*)

(* Function that takes a certif, a list of id pairs, and 
   performs id substitution in the certif *)
let rec subst_id (c : certif) (subst : id * id) : certif =
  match c, subst with
  | (i1, r, cl, p, a) :: tl, (i2, i3) ->
      (* Replace premises with their substitution *)
      let p' = if (List.exists ((=) i2) p) then
        (List.map (fun x -> if x = i2 then i3 else x) p)
      else p in
      (i1, r, cl, p', a) :: subst_id tl subst
  | [], _ -> []
let rec subst_ids (c : certif) (subst : (id * id) list) : certif =
  match subst with
  | h :: t -> subst_ids (subst_id c h) t
  | [] -> c

(* cids stores a list of ids l with id i, if all of l are chained to i *)
let cids : (id, id list) Hashtbl.t = Hashtbl.create 17
let get_cids i =
  try Hashtbl.find cids i
  with | Not_found -> []
let add_cid (i : id) (ci : id) = Hashtbl.add cids i (ci :: (get_cids i))
let clear_cids () = Hashtbl.clear cids

(* Replace every derivation R, to derive (h ^ ~g) v R if it 
  (in)directly uses andn_id as a premise *)
let extend_cl_aux (r : rule) (p : params) (a : args) (pi3 : certif) : rule * clause =
  match r, (get_cl (List.hd p) pi3) with
  | NandAST, Some [Not (And xs)] -> (AndnAST, And xs :: (List.map (fun x -> Not x) xs))
  | OrAST, Some [Or xs] -> (OrpAST, Not (Or xs) :: xs)
  | ImpAST, Some [Imp xs] -> (ImppAST, [Not (Imp xs); Not (List.nth xs 0); List.nth xs 1])
  | Xor1AST, Some [Xor xs] -> (Xorp1AST, Not (Xor xs) :: xs)
  | Nxor1AST, Some [Not (Xor xs)] -> (Xorn1AST, [Xor xs; List.nth xs 0; Not (List.nth xs 1)])
  | Ite1AST, Some [Ite xs] -> (Itep1AST, [Not (Ite xs); List.nth xs 0; List.nth xs 1])
  | Nite1AST, Some [Not (Ite xs)] -> (Iten1AST, [Ite xs; List.nth xs 0; Not (List.nth xs 2)])
  | Xor2AST, Some [Xor xs] -> (Xorp2AST, Not (Xor xs) :: (List.map (fun x -> Not x) xs))
  | Nxor2AST, Some [Not (Xor xs)] -> (Xorn2AST, [Xor xs; Not (List.nth xs 0); Not (List.nth xs 1)])
  | Ite2AST, Some [Ite xs] -> (Itep2AST, [Not (Ite xs); Not (List.nth xs 0); List.nth xs 1])
  | Nite2AST, Some [Not (Ite xs)] -> (Iten2AST, [Ite xs; Not (List.nth xs 0); Not (List.nth xs 1)])
  | Equ1AST, Some [Eq (x, y)] -> (Equp2AST, [Not (Eq (x, y)); Not x; y])
  | Nequ1AST, Some [Not (Eq (x, y))] -> (Equn2AST, [Eq (x, y); x;y])
  | Equ2AST, Some [Eq (x, y)] -> (Equp1AST, [Not (Eq (x, y)); x; Not y])
  | Nequ2AST, Some [Not (Eq (x, y))] -> (Equn1AST, [Eq (x, y); x; Not y])
  | AndAST, Some [And xs] -> let n = int_of_string (List.hd a) in
                              (AndpAST, [Not (And xs); List.nth xs n])
  | NorAST, Some [Not (Or xs)] -> let n = int_of_string (List.hd a) in
                              (OrnAST, [Or xs; List.nth xs n])
  | Nimp1AST, Some [Not (Imp xs)] -> (Impn1AST, [Imp xs; List.nth xs 0])
  | Nimp2AST, Some [Not (Imp xs)] -> (Impn2AST, [Imp xs; Not (List.nth xs 1)])
  | r, Some t -> raise (Debug ("| extend_cl_aux: unexpected rule "^(string_of_rule r)^"to extend_cl, or premise "^(string_of_clause t)^" to the rule at id "^(List.hd p)^" |"))
  | r, None -> raise (Debug ("| extend_cl_aux: rule "^(string_of_rule r)^" has no premise"^" |")) 
let rec extend_cl (andn_id : id) (h : term) (g : term) (pi3 : certif) (pi3og : certif): certif =
  match pi3 with
  | (i, ResoAST, cl, p, a) :: tl when
      (* Resolution that directly uses andn_id *)
      (List.mem andn_id p)
              ||
      (* Resolution that indirectly uses andn_id *)
      (List.exists (fun x -> List.mem x (get_cids andn_id)) p) ->
        add_cid andn_id i;
        (i, ResoAST, ((And [h; Not g])) :: cl, p, a) :: extend_cl andn_id h g tl pi3og
  (* Change ImmBuilddef/ImmBuilddef2/ImmBuildProj rules that use andn_id. For example, not_and:
                                                         ----------------and_neg
   ~(x ^ y) --(andn_id)  --->    ~(x ^ y), (h ^ ~g)      (x ^ y), ~x, ~y  --(1)
  ----------not_and            ---------------------------------------res
    ~x, ~y                                    ~x, ~y, (h ^ ~g)  --(2)
  *)
  | (i, r, cl, p, a) :: tl when
      (match r with
       | NandAST | OrAST | ImpAST | Xor1AST | Nxor1AST | Ite1AST | Nite1AST | Xor2AST
       | Nxor2AST | Ite2AST | Nite2AST | Equ1AST | Nequ1AST | Equ2AST | Nequ2AST 
       | AndAST | NorAST | Nimp1AST | Nimp2AST -> true
       | _ -> false)
              &&
      (* ImmBuilddef(2)/ImmBuildProj that directly uses andn_id *)
      ((List.mem andn_id p)
              ||
      (* ImmBuilddef(2)/ImmBuildProj that indirectly uses andn_id *)
      (List.exists (fun x -> List.mem x (get_cids andn_id)) p)) ->
        add_cid andn_id i;
        let rul, claus = extend_cl_aux r p a pi3og in
        let taut_id = generate_id () in
        (taut_id, rul, claus, [], []) ::                    (* (1) *)
        (i, ResoAST, (List.tl claus), taut_id :: p, []) ::  (* (2) *)
        extend_cl andn_id h g tl pi3og
  | hd :: tl -> hd :: (extend_cl andn_id h g tl pi3og)
  | [] -> []

let process_subproof_aux (andn_id : id) (new_h_id : id) (g_id : id) (pi2 : certif ) (pi3 : certif) (h : term) (g : term) : certif =
  let and_id = get_id (List.hd (List.rev pi3)) in
  let notg_id = generate_id () in
  (* Replace the discharge step proving (~h v g) by a tautological proof of (h ^ ~g) v ~h v g *)
  let t' = [And [h; Not g]; Not h; g] in
  let pi3' = extend_cl andn_id h g pi3 ((andn_id, AndnAST, t', [], []) :: pi3) in
  ((andn_id, AndnAST, t', [], []) ::                        (* (2) *)
    pi3') @
  ((new_h_id, AndAST, [h], [and_id], ["0"]) ::              (* (4) *)
    pi2) @
  [(notg_id, AndAST, [Not g], [and_id], ["1"]);             (* (5) *)
   (generate_id (), ResoAST, [], [g_id; notg_id], [])]      (* (6) *)

let rec process_subproof (c : certif) : certif =
  match c with
  | (i, SubproofAST cert, cl, p, a) :: pi3' ->
      let pi3 = process_subproof pi3' in
      (match List.hd (List.rev cert) with
      | (andn_id, DischargeAST, [Not h; g; ], p', a') ->
          (* Remove first and last element of sub-proof certificate *)
          let certtl = List.tl cert in
          let rev_certtl = List.rev certtl in
          let g_id = get_id (List.hd (List.tl rev_certtl)) in
          let subp = List.rev (List.tl rev_certtl) in
          (* The assumption of the subproof will be derived in a new rule,
             we need to replace all calls to it with calls to the replaced
             rule *)
          let new_h_id = generate_id () in
          let h_id = get_id (List.hd cert) in
          let pi2 = subst_ids subp [(h_id, new_h_id)] in
          process_subproof_aux andn_id new_h_id g_id pi2 pi3 h g
      | _ -> raise (Debug ("| process_subproof: expecting the last step of the certificate to be a discharge step at id "^i^" |")))
  | h :: tl -> h :: process_subproof tl
  | [] -> clear_cids (); []


(* This is a cool function but currently useless since the two places 
   we can use them (process_notnot and process_simpify_ltr) have many case
   specific requirements, but in the future, we may be able to generalize 
   this if we find that it will save some repeated work.contents
   
   remove_step p f:
   remove c, remove all steps s, such that p(s), and
   transform each step s' after s to f s s'.
   Passing s to f allows the transformation to be 
   in terms of the removed step. For example, we want
   to remove the premise corresponding to the id in s 
   from all subsequent resolutions.
   let rec remove_step (p : step -> bool)  (f : step -> step -> step option) (c : certif) : certif =
   match c with
   | s :: cert when p s -> 
       let cert' = List.filter_map (f s) cert in
       remove_step p f cert'
   | s :: cert -> s :: remove_step p f cert
   | [] -> [] *)
 
(* Process _simplify rules from Alethe 
   Each rule has multiple variants, all taking the form
   a <-> b
   To prove a <-> b:
   1. Prove ~a v b via subproof discharge
   2. Prove ~b v a via subproof discharge
   3. Prove a <-> b v ~a v ~b via equiv_neg1
   4. Prove a <-> b by resolving 3,2,1
*)
let simplify_to_subproof (i: id) (a2bi: id) (b2ai: id) (a: term) (b: term) (a2b: certif) (b2a: certif) : certif =
  (* Step 1. *)
  let sp1id = generate_id () in
  let subp1 = (a2bi, AssumeAST, [a], [], []) ::
              (a2b @ 
              [(sp1id, DischargeAST, [Not a; b], [], [])]) in
  (* Step 2. *)
  let sp2id = generate_id () in
  let subp2 = (b2ai, AssumeAST, [b], [], []) ::
              (b2a @ 
              [(sp2id, DischargeAST, [Not b; a], [], [])]) in
  let eqn1id = generate_id () in
  (* subp1 @ subp2 @  *)
  [(generate_id (), SubproofAST subp1, [], [], []);
   (generate_id (), SubproofAST subp2, [], [], []);
  (* Step 3. *)
   (eqn1id, Equn1AST, [Eq (a, b); Not a; Not b], [], []);
  (* Step 4. *)
   (i, ResoAST, [Eq (a,b)], [eqn1id; sp1id; sp2id], [])]
(* Process _simplify rules with the assumption that only their LTR 
   implication is used. Transform a rule of the form:
               i: [a <-> b]                     _simplify
               ...
               m: [~(a <-> b), ~a, b]           equiv_pos2
               ...
               n: [~a, b]                       reso(i,m)
             We want the encoded proof to be:
               i: [~a, B]                       subproof
               ... (remove m) ...
               n: [~a, b]                       reso(i) *)
let simplify_to_subproof_ltr (i: id) (a2bi: id) (a: term) (b: term) (a2b: certif) (tail: certif) : certif =
  let subp = (a2bi, AssumeAST, [a], [], []) ::
              (a2b @ 
              [(i, DischargeAST, [Not a; b], [], [])]) in
  let rec process_tail (c' : certif) : certif =
    match c' with
    | (i, Equp2AST, c, _, _) :: ct when c = [Not (Eq (a,b)); Not a; b] -> 
       let ct' = remove_res_premise i ct in
       process_tail ct'
    | h :: ct -> process_tail ct
    | [] -> [] in
  (i, SubproofAST subp, [], [], []) :: (process_tail tail)
(* are t1 and t2 negations of each other? *)
let is_neg (t1 : term) (t2 : term) : bool =
  match t1, t2 with
  | t, Not t' when t' = t -> true
  | Not t, t' when t' = t -> true
  | _ -> false
(* repeat x n returns list with n x's *)
let repeat (x : 'a) (n : int) : 'a list =
  let rec repeat' (x : 'a) (n : int) (acc : 'a list) : 'a list = 
    match n with
    | 0 -> acc
    | n -> repeat' x (n-1) (x :: acc)
  in
  repeat' x n []
let rec process_simplify (c : certif) : certif =
  match c with
  (* x_1 ^ ... ^ x_n <-> y *)
  | (i, AndsimpAST, cl, p, a) :: tl ->
      (match cl with
       (* T ^ ... ^ T <-> T *)
       | [Eq ((And xs as lhs), (True as rhs))] when (List.for_all ((=) True) xs) ->
          (* T ^ T <-> T
             LTR:
             --true
             T
             RTL:
             -------------and_neg   --asmp  --asmp
             T ^ T, ~T, ~T          T       T
             --------------------------------
                          T ^ T
          *)
          let a2b = [(generate_id (), TrueAST, [True], [], [])] in
          let b2ai = generate_id () in
          let andn_id = generate_id () in
          (* We need 2 things repeated n (= lengh xs) times: 
               1. id of assumption True for resolution
               2. term ~T for and_neg rule *)
          let asmp_ids, ntrues = List.fold_left (fun (a,n) _  -> (b2ai :: a, Not True :: n)) ([],[]) xs in
          let b2a = [(andn_id, AndnAST, (lhs :: ntrues), [], []);
                     (generate_id (), ResoAST, [lhs], andn_id :: asmp_ids, [])]
                      in
          (simplify_to_subproof i (generate_id ()) b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 ^ ... ^ x_n <-> x_1 ^ ... ^ x_n', RHS has all T removed *)
       | [Eq ((And xs as lhs), (And ys as rhs))] when ((List.exists ((=) True) xs) 
            && not (List.exists ((=) True) ys)) ->
          (* x ^ y ^ T <-> x ^ y
             LTR:
             ---------asmp    ---------asmp
             x ^ y ^ T        x ^ y ^ T
             ---------and     ---------and    -------------and_neg
                 x                y           x ^ y, ~x, ~y
                -------------------------------------------res
                                    x ^ y
             RTL:
             -----asmp    -----asmp
             x ^ y        x ^ y
             -----and     -----and     ---true  ---------------------and_neg
               x            y           T       x ^ y ^ T, ~x, ~y, ~T
               ------------------------------------------------------res
                                    x ^ y ^ T
          *)
          let a2bi = generate_id () in
          (* for each y in ys,
               find index ind of first occurrence of y in xs and return
                1. (id', AndAST, [y], [a2bi], ind), where id' is a new id
                2. id'
                3. ~y *)
          let c1, proj_ids1, projnegl1 = List.fold_left 
            (fun (s,i,n) y -> 
              let ind = findi y xs in
              let id' = generate_id () in
              ((id', AndAST, [y], [a2bi], [string_of_int ind]) :: s,
               id' :: i,
               Not y :: n))
              ([],[],[]) ys in
          let andn_id1 = generate_id () in
          let a2b = c1 @ 
                    [(andn_id1, AndnAST, rhs :: projnegl1, [], []);
                     (generate_id (), ResoAST, [rhs], andn_id1 :: proj_ids1, [])] in
          let b2ai = generate_id () in
          let true_id = generate_id () in
          (* for each x in xs
               if x is T, then return 1. true_id 2. ~x, where true_id refers to the id of the derivation of T
               else
                find index ind of first occurrence of x in ys and return
                 1. (id', AndAST, [x], [b2ai], ind), where id' is a new id
                 2. id'
                 3. ~x *)
          let c2, proj_ids2, projnegl2 = List.fold_left 
            (fun (s,i,n) x ->
              if x = True then
                (s, true_id :: i, Not x :: n)
              else
                let ind = findi x ys in
                let id' = generate_id () in
                ((id', AndAST, [x], [b2ai], [string_of_int ind]) :: s,
                 id' :: i,
                 Not x :: n))
            ([],[],[]) xs in
          let andn_id2 = generate_id () in
          let b2a = c2 @
                    [(true_id, TrueAST, [True], [], []);
                     (andn_id2, AndnAST, lhs :: projnegl2, [], []);
                     (generate_id (), ResoAST, [lhs], andn_id2 :: proj_ids2, [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 ^ ... ^ x_n <-> x_1 ^ ... ^ x_n', RHS has all repeated literals removed *)
       | [Eq ((And xs as lhs), (And ys as rhs))] when ((List.exists (fun x -> (List.exists (fun y -> y = x) xs)) xs)
          && not (List.exists (fun x -> (List.exists (fun y -> y = x) ys)) ys)) ->
          (* x ^ y ^ x <-> x ^ y
             LTR:
             ---------asmp    ---------asmp
             x ^ y ^ x        x ^ y ^ x
             ---------and     ---------and    -------------and_neg
                 x                y           x ^ y, ~x, ~y
                 ------------------------------------------res
                                  x ^ y
             RTL:
             -----asmp    -----asmp    -----asmp
             x ^ y        x ^ y        x ^ y
             -----and     -----and     -----and   ---------------------and_neg
               x            y            x        x ^ y ^ x, ~x, ~y, ~x
               --------------------------------------------------------res
                                      x ^ y ^ x
          *)
          let a2bi = generate_id () in
          (* for each y in ys,
               find index ind of first occurrence of y in xs and return
                1. (id', AndAST, [y], [a2bi], ind), where id' is a new id
                2. id'
                3. ~y *)
          let c1, proj_ids1, projnegl1 = List.fold_left 
            (fun (s,i,n) y -> 
              let ind = findi y xs in
              let id' = generate_id () in
              ((id', AndAST, [y], [a2bi], [string_of_int ind]) :: s,
               id' :: i,
               Not y :: n))
              ([],[],[]) ys in
          let andn_id1 = generate_id () in
          let a2b = c1 @
                    [(andn_id1, AndnAST, rhs :: projnegl1, [], []);
                     (generate_id (), ResoAST, [rhs], andn_id1 :: proj_ids1, [])] in
          let b2ai = generate_id () in
          (* for each x in xs
               find index ind of first occurrence of x in ys and return
                1. (id', AndAST, [x], [b2ai], ind), where id' is a new id
                2. id'
                3. ~x *)
          let c2, proj_ids2, projnegl2 = List.fold_left 
            (fun (s,i,n) x ->
              let ind = findi x ys in
              let id' = generate_id () in
              ((id', AndAST, [x], [b2ai], [string_of_int ind]) :: s,
                 id' :: i,
                 Not x :: n))
            ([],[],[]) xs in
          let andn_id2 = generate_id () in
          let b2a = c2 @
                    [(andn_id2, AndnAST, lhs :: projnegl2, [], []);
                     (generate_id (), ResoAST, [lhs], andn_id2 :: proj_ids2, [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 ^ ... F ... ^ x_n <-> F *)
       | [Eq ((And xs as lhs), (False as rhs))] when (List.exists ((=) False) xs) ->
          (* x ^ F <-> F
             LTR:
             -----asmp
             x ^ F
             RTL: can't derive x from F without an absurd rule which we don't have.
             We simplify assuming that this equivalence is only used as an LTR
          *)
          let a2bi = generate_id () in
          let ind = findi False xs in
          let a2b = [(generate_id (), AndAST, [False], [a2bi], [string_of_int ind])] in
          (match (simplify_to_subproof_ltr i a2bi lhs rhs a2b tl) with
           | h :: t -> h :: process_simplify t
           | [] -> [])
       (* x_1 ^ ... x_i ... x_j ... ^ x_n <-> F, if x_i = ~x_j *)
       | [Eq ((And xs as lhs), (False as rhs))] when 
            (List.exists (fun x -> (List.exists (fun y -> is_neg y x) xs)) xs) ->
          (* x ^ ~x <-> F
             LTR:
                        ------ass
                        x ^ ~x
                        ------and ---------imp_neg1
                          ~x      x -> F, x
             ------ass  -------------------res
             x ^ ~x            x -> F
             ------and         ------imp
               x                ~x, F
             -------------------------res
                          F
             RTL: can't derive x and ~x from F without an absurd rule which we don't have
             Assume that this equivalence is only used as an LTR rewrite
          *)
          let a2bi = generate_id () in
          let x = List.find (fun x -> (List.exists (fun y -> y = Not x) xs)) xs in
          let x_id = string_of_int (findi x xs) in
          let nx_id = string_of_int (findi (Not x) xs) in
          let and_id1 = generate_id () in
          let and_id2 = generate_id () in
          let impn_id = generate_id () in
          let res_id = generate_id () in
          let imp_id = generate_id () in
          let a2b = [(and_id1, AndAST, [x], [a2bi], [x_id]);
                     (and_id2, AndAST, [Not x], [a2bi], [nx_id]);
                     (impn_id, Impn1AST, [Imp [x; False]; x], [], []);
                     (res_id, ResoAST, [Imp [x; False]], [and_id2; impn_id], []);
                     (imp_id, ImpAST, [Not x; False], [res_id], []);
                     (generate_id (), ResoAST, [False], [and_id1; imp_id], [])] in
          (match (simplify_to_subproof_ltr i a2bi lhs rhs a2b tl) with
           | h :: t -> h :: process_simplify t
           | [] -> [])
       | [Eq _] -> (i, AndsimpAST, cl, p, a) :: process_simplify tl
       | _ -> raise (Debug ("| process_simplify: expecting argument of and_simplify to be an equivalence at id "^i^" |")))
  (* x_1 v ... v x_n <-> y *)
  | (i, OrsimpAST, cl, p, a) :: tl ->
      (match cl with
       (* F v ... v F <-> F *)
       | [Eq ((Or xs as lhs), (False as rhs))] when (List.for_all ((=) False) xs) ->
          (* F v F <-> F
             LTR: 
             -----asmp  ---false  --------------or_pos
             F v F      ~F        ~(F v F), F, F
             -----------------------------------res
                              F
             RTL:
             --asmp   ---------or_neg
             F        F v F, ~F
             ------------------res
                    F v F
          *)
           let a2bi = generate_id () in
           let f_id = generate_id () in
           let orp_id = generate_id () in
           (* We need 2 things repeated around n (= lengh xs) times: 
                1. id of F rule (f_id) for resolution (n-1 times)
                2. term F for or_pos rule (n times) *)
           let f_ids, nfalses = List.fold_left (fun (f,n) _ -> (f_id :: f, False :: n)) ([],[]) xs in
           let a2b = [(f_id, FalsAST, [Not False], [], []);
                      (orp_id, OrpAST, (Not lhs) :: nfalses, [],[]);
                      (generate_id (), ResoAST, [rhs], orp_id :: a2bi :: (List.tl f_ids), [])] in
           let b2ai = generate_id () in
           let orn_id = generate_id () in
           let b2a = [(orn_id, OrnAST, (lhs :: [Not rhs]), [], [string_of_int 0]);
                      (generate_id (), ResoAST, [lhs], [orn_id; b2ai], [])] in
           (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 v ... v x_n <-> x_1 v ... x_n', RHS has all F removed *)
       | [Eq ((Or xs as lhs), (Or ys as rhs))] when ((List.exists ((=) False) xs) 
            && not (List.exists ((=) False) ys)) ->
          (* x v y v F <-> x v y
             LTR:
             ---------asmp
             x v y v F
             ---------or    --false
             x v y v F      ~F             
             -----------------res
                    x v y
            RTL:
            -----asmp
            x v y
            -----or   ---------------or_neg   ---------------or_neg
             x,y      (x v y v x), ~x         (x v y v x), ~y
             ------------------------------------------------res
                                x v y v x
          *)
           let a2bi = generate_id () in
           let or_id1 = generate_id () in
           let f_id = generate_id () in
           (* number of F in xs *)
           let f_cnt = List.fold_left (fun n x -> if x = False then n + 1 else n) 0 xs in
           let a2b = [(or_id1, OrAST, xs, [a2bi], []);
                      (f_id, FalsAST, [False], [], []);
                      (generate_id (), ResoAST, [rhs], or_id1 :: (repeat f_id f_cnt), [])] in
           let b2ai = generate_id () in
           let or_id2 = generate_id () in
           (* for each y in ys,
                find index ind of first occurrence of y in xs and return
                 1. (id', OrnAST, [lhs; ~y], [], [ind]), where id' is a new id
                 2. id' *)
           let c, proj_ids = List.fold_left 
             (fun (s,i) y -> 
               let ind = findi y xs in
               let id' = generate_id () in
               ((id', OrnAST, [lhs; Not y], [], [string_of_int ind]) :: s,
                id' :: i))
             ([],[]) ys in
           let b2a = c @
                     [(or_id2, OrAST, ys, [b2ai], []);
                      (generate_id (), ResoAST, [lhs], or_id2 :: proj_ids, [])] in
           (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 v ... v x_n <-> x_1 v ... x_n', RHS has all repeated literals removed *)
       | [Eq ((Or xs as lhs), (Or ys as rhs))] when ((List.exists (fun x -> (List.exists (fun y -> y = x) xs)) xs)
          && not (List.exists (fun x -> (List.exists (fun y -> y = x) ys)) ys)) ->
          (* x v y v x <-> x v y
             SMTCoq removes duplicates in clauses, but in LTR we don't construct an or in the end, 
             I think this should be okay. TODO check with Chantal
             LTR:
             ---------asmp
             x v y v x
             ---------or
                x,y
             RTL:
             -----asmp
             x v y
             -----or  ---------------or_neg   ---------------or_neg
              x,y     (x v y v x), ~x         (x v y v x), ~y
              -----------------------------------------------res
                                x v y v x
          *)
           let a2bi = generate_id () in
           let or_id1 = generate_id () in
           let a2b = [(or_id1, OrAST, xs, [a2bi], [])] in
           let b2ai = generate_id () in
           let or_id2 = generate_id () in
           (* for each y in ys,
               find index ind of first occurrence of y in xs and return
                1. (id', OrnAST, [y], [b2ai], [ind]), where id' is a new id
                2. id' *)
           let c, proj_ids = List.fold_left 
            (fun (s,i) y -> 
              let ind = findi y xs in
              let id' = generate_id () in
              ((id', OrnAST, [y], [b2ai], [string_of_int ind]) :: s,
               id' :: i))
              ([],[]) ys in
           let b2a = (or_id2, OrAST, ys, [b2ai], []):: c @
                     [(generate_id (), ResoAST, [lhs], or_id2 :: proj_ids, [])] in 
           (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 v ... T ... x_n <-> T *)
       | [Eq ((Or xs as lhs), (True as rhs))] when (List.exists ((=) True) xs) ->
          (* x v T <-> T
             LTR:
             --true
             T
             RTL:
             --asmp   -----------or_neg
             T        (x v T), ~T
             --------------------res
                    x v T
          *)
          let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
          let orn_id = generate_id () in
          let b2ai = generate_id () in
          let orn_a = string_of_int (findi True xs) in
          let b2a = [(orn_id, OrnAST, [lhs; Not True], [], [orn_a]);
                     (generate_id (), ResoAST, [lhs], [b2ai; orn_id], [])] in
          (simplify_to_subproof i (generate_id ()) b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 v ... x_i ... x_j ... x_n <-> T, if x_i = ~x_j *)
       | [Eq ((Or xs as lhs), (True as rhs))] when 
          (List.exists (fun x -> (List.exists (fun y -> is_neg y x) xs)) xs) ->
          (* x v ~x <-> T
             LTR:
             --true
              T
             RTL:
             --------------or_neg -------------or_neg
             (x v ~x), ~x         (x v ~x), ~~x
             ----------------------------------res
                           x v ~x
          *)
          let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
          let orn_id1 = generate_id () in
          let orn_id2 = generate_id () in
          let x = List.find (fun x -> (List.exists (fun y -> y = Not x) xs)) xs in
          let x_id = string_of_int (findi x xs) in
          let nx_id = string_of_int (findi (Not x) xs) in
          let b2a = [(orn_id1, OrnAST, [lhs; Not x], [], [x_id]);
                     (orn_id2, OrnAST, [lhs; x], [], [nx_id]);
                     (generate_id (), ResoAST, [lhs], [orn_id1; orn_id2], [])] in
          (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl
       | [Eq _] -> (i, OrsimpAST, cl, p, a) :: process_simplify tl
       | _ -> raise (Debug ("| process_simplify: expecting argument of or_simplify to be an equivalence at id "^i^" |")))
  (* ~x <-> y *)
  | (i, NotsimpAST, cl, p, a) :: tl ->
      (match cl with
       (* ~F <-> T *)
          (*
             LTR:
             --true
             T
             RTL:
             --false
             ~F
          *)
       | [Eq ((Not False as lhs), (True as rhs))] ->
          let a2b = [(generate_id (), TrueAST, [True], [], [])] in
          let b2a = [(generate_id (), FalsAST, [Not False], [], [])] in
          (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl
       (* ~T <-> F *)
       | [Eq ((Not True as lhs), (False as rhs))] ->
          (*
             LTR:
             --asmp ---------imp_neg1
             ~T     T -> F, T
             ----------------res
                  T -> F
                  -----imp  --true
                  ~T, F      T    
                  ------------res
                        F
             RTL: can't derive ~T from F without an absurd rule which we don't have.
             Assume that this equivalence is only used as an LTR rewrite
          *)
          let a2bi = generate_id () in
          let impn_id = generate_id () in
          let res_id = generate_id () in
          let imp_id = generate_id () in
          let t_id = generate_id () in
          let a2b = [(impn_id, Impn1AST, [Imp [True; False]; True], [], []);
                     (res_id, ResoAST, [Imp [True; False]], [a2bi;impn_id], []);
                     (imp_id, ImpAST, [Not True; False], [res_id], []);
                     (t_id, TrueAST, [True], [], []);
                     (generate_id (), ResoAST, [False], [imp_id; t_id], [])] in
          (match (simplify_to_subproof_ltr i a2bi lhs rhs a2b tl) with
           | h :: t -> h :: process_simplify t
           | [] -> [])
       (* ~(~x) <-> x handled by process_notnot*)
       | [Eq _] -> (i, NotsimpAST, cl, p, a) :: process_simplify tl
       | _ -> raise (Debug ("| process_simplify: expecting argument of and_simplify to be an equivalence at id "^i^" |")))
  | (i, ImpsimpAST, cl, p, a) :: tl ->
      (match cl with
       (* (~x -> y) <-> (y -> x) *)
       | [Eq ((Imp [Not x; y] as lhs), (Imp [b; a] as rhs))] when (x = a && y = b) ->
          (*
             LTR:
             -------asmp
             ~x -> y
             -------imp   ---------imp_neg1   ----------imp_neg2
             ~~x, ~y      y -> x, y           y -> x, ~x
             -------------------------------------------res
                                 y -> x
             RTL:
             ------asmp
             y -> x
             ------imp     ------------imp_neg1  -------------imp_neg2
             ~y, x         ~x -> ~y, ~x          ~x -> ~y, ~~y
             -------------------------------------------------res
                                 ~x -> ~y
          *)
          let a2bi = generate_id () in
          let impi1 = generate_id () in
          let impn1i1 = generate_id () in
          let impn2i1 = generate_id () in
          let a2b = [(impi1, ImpAST, [x; Not y], [a2bi], []);
                     (impn1i1, Impn1AST, [rhs; y], [], []);
                     (impn2i1, Impn2AST, [rhs; Not x], [], []);
                     (generate_id (), ResoAST, [rhs], [impi1; impn1i1; impn2i1], [])] in
          let b2ai = generate_id () in
          let impi2 = generate_id () in
          let impn1i2 = generate_id () in
          let impn2i2 = generate_id () in
          let b2a = [(impi2, ImpAST, [Not y; x], [b2ai], []);
                     (impn1i2, Impn1AST, [lhs; Not x], [], []);
                     (impn2i2, Impn2AST, [lhs; y], [], []);
                     (generate_id (), ResoAST, [lhs], [impi2; impn1i2; impn2i2], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (F -> x) <-> T *)
       | [Eq ((Imp [False; x] as lhs), (True as rhs))] ->
          (*
             LTR:
             --true
             T
             RTL:
             ---------imp_neg1  --false
             F -> x, F          ~F
             ---------------------res
                     F -> x
          *)
          let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
          let impni = generate_id () in
          let fi = generate_id () in
          let b2a = [(impni, Impn1AST, [Imp [False; x]; False], [], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [Imp [False; x]], [], [])] in
          (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl
       (* (x -> T) <-> T *)
       | [Eq ((Imp [x; True] as lhs), (True as rhs))] ->
          (*
             LTR:
             --true
             T
             RTL:
             --asmp   ----------imp_neg2
             T        x -> T, ~T
             -------------------res
                   x -> T
          *)
          let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
          let b2ai = generate_id () in
          let impni = generate_id () in
          let b2a = [(impni, Impn2AST, [lhs; Not True], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai;impni], [])] in
          (simplify_to_subproof i (generate_id ()) b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (T -> x) <-> x *)
       | [Eq ((Imp [True; x] as lhs), (a as rhs))] when (x = a) ->
          (*
             LTR:
             ------asmp
             T -> x
             ------implies   --true
             ~T, x            T
             -------------------res
                       x
             RTL:
             --asmp   -----------imp_neg2
             x        T -> x, ~x
             -------------------res
                    T -> x
          *)
          let a2bi = generate_id () in
          let impi = generate_id () in
          let ti = generate_id () in
          let a2b = [(impi, ImpAST, [Not True; x], [a2bi], []);
                     (ti, TrueAST, [True], [], []);
                     (generate_id (), ResoAST, [rhs], [impi; ti], [])] in
          let b2ai = generate_id () in
          let impni = generate_id () in
          let b2a = [(impni, Impn2AST, [lhs; Not x], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai; impni], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x -> F) <-> ~x *)
       | [Eq ((Imp [x;False] as lhs), (Not a as rhs))] when (x = a) ->
          (*
             LTR:
             ------asmp
             x -> F
             ------imp  --false
             ~x, F      ~F
             -------------res
                   ~x
             RTL:
             --asmp   ---------imp_neg1
             ~x       x -> F, x
             ------------------res
                  x -> F
          *)
          let a2bi = generate_id () in
          let imp_id = generate_id () in
          let f_id = generate_id () in
          let a2b = [(imp_id, ImpAST, [Not x; False], [a2bi], []);
                     (f_id, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [rhs], [imp_id; f_id], [])] in
          let b2ai = generate_id () in
          let impn_id = generate_id () in
          let b2a = [(impn_id, Impn1AST, [lhs; x], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai;impn_id], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x -> x) <-> T *)
       | [Eq ((Imp [x;a] as lhs), (True as rhs))] when (x = a) ->
          (*
             LTR:
             --true
             T
             RTL:
             ---------imp_neg1  ----------imp_neg1
             x -> x, x          x -> x, ~x
             -----------------------------res
                         x -> x
          *)
          let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
          let impni1 = generate_id () in
          let impni2 = generate_id () in
          let b2a = [(impni1, Impn1AST, [Imp [x;x]; x], [], []);
                     (impni2, Impn1AST, [Imp [x;x]; Not x], [], []);
                     (generate_id (), ResoAST, [lhs], [impni1;impni2], [])] in
          (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl
       (* (~x -> x) <-> x *)
       | [Eq ((Imp [Not x;a] as lhs), (b as rhs))] when (x = a && x = b) ->
          (* TODO: check that ~~x is stored as x and duplicates are removed
             LTR:
             -------asmp  ------------------imp_pos
             ~x -> x      ~(~x -> x), ~~x, x
             -------------------------------res
                            x
             RTL:
             --asmp -----------imp_neg1
             x      ~x -> x, ~x
             ------------------res
                  ~x -> x
          *)
          let a2bi = generate_id () in
          let imppi = generate_id () in
          let a2b = [(imppi, ImppAST, [Not lhs; x; x], [], []);
                     (generate_id (), ResoAST, [rhs], [a2bi;imppi],[])] in
          let b2ai = generate_id () in
          let impni = generate_id () in
          let b2a = [(impni, Impn1AST, [lhs; Not x], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai;impni], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x -> ~x) <-> ~x *)
       | [Eq ((Imp [x; Not a] as lhs), (Not b as rhs))] when (x = a && x = b) ->
          (*
             LTR:
             -------asmp  ------------------imp_pos
             x -> ~x      ~(x -> ~x), ~x, ~x
             -------------------------------res
                           ~x
             RTL:
             --asmp   ----------imp_neg1
             ~x       x -> ~x, x
             -------------------res
                  x -> ~x
          *)
          let a2bi = generate_id () in
          let imppi = generate_id () in
          let a2b = [(imppi, ImppAST, [Not lhs; Not x; Not x], [], []);
                     (generate_id (), ResoAST, [rhs], [a2bi; imppi], [])] in
          let b2ai = generate_id () in
          let impni = generate_id () in
          let b2a = [(impni, Impn1AST, [lhs; x], [], []);
                     (generate_id (), ResoAST, [lhs], [], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ((x -> y) -> y) <-> (x v y) *)
       | [Eq ((Imp [Imp [x;y]; a] as lhs), (Or [b;c] as rhs))] when (y = a && x = b && y = c) ->
          (*
             LTR:
             -------------asmp
             (x -> y) -> y
             -------------imp   ---------or_neg   ---------imp_neg1   ---------or_neg
             ~(x -> y), y       x v y, ~y         x -> y, x           x v y, ~x
             ------------------------------------------------------------------res    
                                            x v y

             RTL:
             -----asmp  
             x v y      
             -----or    ---------------------imp_neg1   ----------------imp_pos   -----------------imp_neg2
             x, y       (x -> y) -> y, x -> y           ~(x -> y), ~x, y          (x -> y) -> y, ~y       
             --------------------------------------------------------------------------------------res
                                                (x -> y) -> y
          *)
          let a2bi = generate_id () in
          let impi = generate_id () in
          let orni1 = generate_id () in
          let impni1 = generate_id () in
          let orni2 = generate_id () in
          let a2b = [(impi, ImpAST, [Not (Imp [x;y]); y], [a2bi], []);
                     (orni1, OrnAST, [Or [x;y]; Not y], [], []);
                     (impni1, Impn1AST, [Imp [x;y]; x], [], []);
                     (orni2, OrnAST, [Or [x;y]; Not x], [], []);
                     (generate_id (), ResoAST, [rhs], [impi;orni1;impni1;orni2], [])] in
          let b2ai = generate_id () in
          let ori = generate_id () in
          let impni2 = generate_id () in
          let imppi = generate_id () in
          let impni3 = generate_id () in
          let b2a = [(ori, OrAST, [x; y], [b2ai], []);
                     (impni2, Impn1AST, [lhs; Imp [x;y]], [], []);
                     (imppi, ImppAST, [Not (Imp [x;y]); Not x; y], [], []);
                     (impni3, Impn2AST, [lhs; Not y], [], []);
                     (generate_id (), ResoAST, [lhs], [ori;impni2;imppi;impni3], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       | [Eq _] -> (i, ImpsimpAST, cl, p, a) :: process_simplify tl
       | _ -> raise (Debug ("| process_simplify: expecting argument of implies_simplify to be an equivalence at id "^i^" |")))
  (* (x <-> y) <-> z *)
  | (i, EqsimpAST, cl, p, a) :: tl ->
      (match cl with
       (* (~x <-> ~y) <-> (x <-> y) *)
       (* (x <-> x) <-> T *)
       (* (x <-> ~x) <-> F *)
       (* (~x <-> x) <-> F *)
       (* (T <-> x) <-> x *)
       (* (x <-> T) <-> x *)
       (* (F <-> x) <-> ~x *)
       (* (x <-> F) <-> ~x *)
       | [Eq _] -> (i, EqsimpAST, cl, p, a) :: process_simplify tl
       | _ -> raise (Debug ("| process_simplify: expecting argument of equiv_simplify to be an equivalence at id "^i^" |")))
  (* x <-> y *)
  | (i, BoolsimpAST, cl, p, a) :: tl ->
      (match cl with
       (* ~(x -> y) <-> (x ^ ~y) *)
       | [Eq ((Not (Imp [x; y]) as lhs), (And [a; Not b] as rhs))] when (x = a && y = b) ->
          (*
             LTR:
             ---------asmp  -----------imp_neg1   ---------asmp   ------------imp_neg2
             ~(x -> y)      (x -> y), x           ~(x -> y)       (x -> y), ~y
             --------------------------res        ----------------------------res     ---------------and_neg
                          x                                     ~y                    x ^ ~y, ~x, ~~y
                          ---------------------------------------------------------------------------res
                                                              x ^ ~y
             RTL:
             -------asmp  ------------and_pos   ------asmp    -------------and_pos
             x ^ ~y       ~(x ^ ~y), x          x ^ ~y        ~(x ^ ~y), ~y
             -------------------------res       ---------------------------res    ----------------imp_pos
                         x                                   ~y                   ~(x -> y), ~x, y
                         -------------------------------------------------------------------------res
                                                          ~(x -> y)
          *)
          let a2bi = generate_id () in
          let impn1i = generate_id () in
          let impn2i = generate_id () in
          let res_1i = generate_id () in
          let res_2i = generate_id () in
          let andni = generate_id () in
          let a2b = [(impn1i, Impn1AST, [Imp [x;y]; x], [], []);
                     (res_1i, ResoAST, [x], [impn1i;a2bi], []);
                     (impn2i, Impn2AST, [Imp [x;y]; Not y], [], []);
                     (res_2i, ResoAST, [Not y], [impn2i;a2bi], []);
                     (andni, AndnAST, [And [x;Not y]; Not x; Not (Not y)], [], []);
                     (generate_id (), ResoAST, [rhs], [andni;res_1i;res_2i], [])] in
          let b2ai = generate_id () in
          let andp_1i = generate_id () in
          let res_3i = generate_id () in
          let andp_2i = generate_id () in
          let res_4i = generate_id () in
          let imppi = generate_id () in
          let b2a = [(andp_1i, AndpAST, [Not rhs; x], [], []);
                     (res_3i, ResoAST, [x], [andp_1i;b2ai], []);
                     (andp_2i, AndpAST, [Not rhs; Not y], [], []);
                     (res_4i, ResoAST, [Not y], [andp_2i;b2ai], []);
                     (imppi, ImppAST, [lhs; Not x; y], [], []);
                     (generate_id (), ResoAST, [lhs], [imppi;res_3i;res_4i], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ~(x v y) <-> (~x ^ ~y) *)
       | [Eq ((Not (Or [x;y]) as lhs), (And [Not a;Not b] as rhs))] when (x = a && y = b) ->
         (*
            LTR:
            --------asmp  ---------or_neg   --------asmp  ---------or_neg
            ~(x v y)      x v y, ~x         ~(x v y)      x v y, ~y
            -----------------------res      -----------------------res    -----------------and_neg
                       ~x                               ~y                ~x ^ ~y, ~~x, ~~y
                       --------------------------------------------------------------------res
                                                      ~x ^ ~y
            RTL:
            -------asmp   --------------and_pos   -------asmp   --------------and_pos
            ~x ^ ~y       ~(~x ^ ~y), ~x          ~x ^ ~y       ~(~x ^ ~y), ~y
            ----------------------------res       ------------------------------res   --------------or_pos
                        ~x                                      ~y                    ~(x v y), x, y
                        ----------------------------------------------------------------------------res
                                                        ~(x v y)
         *)
         let a2bi = generate_id () in
         let orn_1i = generate_id () in
         let res_1i = generate_id () in
         let orn_2i = generate_id () in
         let res_2i = generate_id () in
         let andni = generate_id () in
         let a2b = [(orn_1i, OrnAST, [Or [x;y]; Not x], [], []);
                    (res_1i, ResoAST, [Not x], [orn_1i;a2bi], []);
                    (orn_2i, OrnAST, [Or [x;y]; Not y], [], []);
                    (res_2i, ResoAST, [Not y], [orn_2i;a2bi], []);
                    (andni, AndnAST, [rhs; Not x; Not y], [], []);
                    (generate_id (), ResoAST, [rhs], [andni;res_1i;res_2i], [])] in
         let b2ai = generate_id () in
         let andp_1i = generate_id () in
         let res_3i = generate_id () in
         let andp_2i = generate_id () in
         let res_4i = generate_id () in
         let orpi = generate_id () in
         let b2a = [(andp_1i, AndpAST, [Not rhs; Not x], [], []);
                    (res_3i, ResoAST, [Not x], [andp_1i;b2ai], []);
                    (andp_2i, AndpAST, [Not rhs; Not y], [], []);
                    (res_4i, ResoAST, [Not y], [andp_2i;b2ai], []);
                    (orpi, OrpAST, [lhs; x; y], [], []);
                    (generate_id (), ResoAST, [lhs], [orpi;res_3i;res_4i], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ~(x ^ y) <-> (~x v ~y) *)
       | [Eq ((Not (And [x;y]) as lhs), (Or [Not a;Not b] as rhs))] when (x = a && y = b) ->
         (*
            LTR:
            --------asmp  ---------------and_neg  ------------or_neg  ------------or_neg
            ~(x ^ y)      (x ^ y), ~x, ~y         ~x v ~y, ~~x        ~x v ~y, ~~y
            ----------------------------------------------------------------------res
                                              ~x v ~y
            RTL:
            -------asmp   ------------------or_pos    -----------and_pos  -----------and_pos
            ~x v ~y       ~(~x v ~y), ~x, ~y          ~(x ^ y), x         ~(x ^ y), y
            -------------------------------------------------------------------------res
                                             ~(x ^ y)
         *)
         let a2bi = generate_id () in
         let andni = generate_id () in
         let orni1 = generate_id () in
         let orni2 = generate_id () in
         let a2b = [(andni, AndnAST, [And [x;y]; Not x; Not y], [], []);
                    (orni1, OrnAST, [rhs; x], [], []);
                    (orni2, OrnAST, [rhs; y], [], []);
                    (generate_id (), ResoAST, [rhs], [a2bi; andni; orni1; orni2], [])] in
         let b2ai = generate_id () in
         let orpi = generate_id () in
         let andpi1 = generate_id () in
         let andpi2 = generate_id () in
         let b2a = [(orpi, OrpAST, [Not rhs; Not x; Not y], [], []);
                    (andpi1, AndpAST, [lhs; x], [], ["1"]);
                    (andpi1, AndpAST, [lhs; y], [], ["2"]);
                    (generate_id (), ResoAST, [lhs], [b2ai; orpi; andpi1; andpi2], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
      (* (x -> (y -> z)) <-> ((x ^ y) -> z) *)
      (* ((x -> y) -> z) <-> (x v y) *)
      (* (x ^ (y -> z)) <-> (x ^ y) *)
      (* ((x -> y) ^ x) <-> (x ^ y) *)
      | [Eq _] -> (i, BoolsimpAST, cl, p, a) :: process_simplify tl
      | _ -> raise (Debug ("| process_simplify: expecting argument of bool_simplify to be an equivalence at id "^i^" |"))
      )
  (* x <-> y *)
  | (i, ConndefAST, cl, p, a) :: tl ->
      (match cl with
      (* x xor y <-> (~x ^ y) v (x ^ y) *)
      (* x <-> y <-> (x -> y) ^ (y -> x) *)
      (* ite c x y <-> (c -> x) ^ (~c -> y) *)
      (* forall x_1, ..., x_n. F <-> ~ exists x_1, ..., x_n. ~F *)
      | [Eq _] -> (i, ConndefAST, cl, p, a) :: process_simplify tl
      | _ -> raise (Debug ("| process_simplify: expecting argument of connective_def to be an equivalence at id "^i^" |"))
      )
  | h :: tl -> h :: process_simplify tl
  | nil -> nil


(* Final processing and linking of AST *)

let preprocess_certif (c: certif) : certif =
  Printf.printf ("Certif before preprocessing: \n%s\n") (string_of_certif c);
  try 
  (let c1 = store_shared_terms c in
  Printf.printf ("Certif after storing shared terms: \n%s\n") (string_of_certif c1);
  let c2 = process_fins c1 in
  Printf.printf ("Certif after process_fins: \n%s\n") (string_of_certif c2);
  let c3 = process_simplify c2 in
  Printf.printf ("Certif after process_simplify: \n%s\n") (string_of_certif c3);
  let c4 = process_subproof c3 in
  Printf.printf ("Certif after process_subproof: \n%s\n") (string_of_certif c4);
  let c5 = process_notnot c4 in
  Printf.printf ("Certif after process_notnot: \n%s\n") (string_of_certif c5);
  let c6 = process_cong c5 in
  Printf.printf ("Certif after process_cong: \n%s\n") (string_of_certif c6);
  let c7 = process_proj c6 in
  Printf.printf ("Certif after process_proj: \n%s\n") (string_of_certif c7);
  c7) with
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