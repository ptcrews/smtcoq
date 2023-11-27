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
  | ArithpolynormAST
  | LiaRewriteAST
  | BindAST
  | FinsAST
  | QcnfAST
  | AnchorAST
  | AllsimpAST
  | SameAST
  | HoleAST
  | WeakenAST
  | FlattenAST
  | DischargeAST
  | SubproofAST of certif
and step = id * rule * clause * params * args
and certif = step list

let mk_cl (ts : term list) : clause = ts
let mk_step (s : (id * rule * clause * params * args)) : step = s
let mk_cert (c : step list) : certif = c

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


(* Store shared terms *)
let sterms : (string, term) Hashtbl.t = Hashtbl.create 17
let get_sterm s =
  try Hashtbl.find sterms s
  with 
  | Not_found -> raise (Debug 
      ("| get_sterm : can't find "^s^" |"))
let add_sterm s t = Hashtbl.add sterms s t
let clear_sterms () = Hashtbl.clear sterms

(* Get expression modulo aliasing *)
let rec get_expr = function
  | Not t -> Not (get_expr t)
  | And ts -> And (List.map get_expr ts)
  | Or ts -> Or (List.map get_expr ts)
  | Imp ts -> Imp (List.map get_expr ts)
  | Xor ts -> Xor (List.map get_expr ts)
  | Ite ts -> Ite (List.map get_expr ts)
  | Forall (ls, t) -> Forall (ls, (get_expr t))
  | Eq (t1, t2) -> Eq (get_expr t1, get_expr t2)
  | App (s, ts) -> App (s, (List.map get_expr ts))
  | STerm t -> 
      let t' = try get_sterm t with
               | Debug s -> 
                raise (Debug ("| get_expr: can't find sterm "^t^" |"^s)) in
      get_expr t'
  | NTerm (s, t) -> NTerm (s, (get_expr t))
  | Lt (t1, t2) -> Lt (get_expr t1, get_expr t2)
  | Leq (t1, t2) -> Leq (get_expr t1, get_expr t2)
  | Gt (t1, t2) -> Gt (get_expr t1, get_expr t2)
  | Geq (t1, t2) -> Geq (get_expr t1, get_expr t2)
  | UMinus t -> UMinus (get_expr t)
  | Plus (t1, t2) -> Plus (get_expr t1, get_expr t2)
  | Minus (t1, t2) -> Minus (get_expr t1, get_expr t2)
  | Mult (t1, t2) -> Mult (get_expr t1, get_expr t2)
  | e -> e

let get_expr_cl (c : clause) = List.map get_expr c


(* List Utilities *)
(* findi x l finds the index of x in l
   Note that it checks for syntactic equality of terms, not modulo
   alpha renaming *)
   let findi (p : 'a -> bool) (l : 'a list) : int = 
    let rec findi' (p : 'a -> bool) (l : 'a list) (n : int) : int = 
      match l with
      | h :: t -> if p h then n else findi' p t (n+1)
      | [] -> raise (Debug ("| findi: element not found |")) in
    findi' p l 0


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
  | ArithpolynormAST -> "ArithpolynormAST"
  | LiaRewriteAST -> "LiaRewriteAST"
  | BindAST -> "BindAST"
  | FinsAST -> "FinsAST"
  | QcnfAST -> "QcnfAST"
  | AllsimpAST -> "AllsimpAST"
  | SameAST -> "SameAST"
  | HoleAST -> "HoleAST"
  | WeakenAST -> "WeakenAST"
  | FlattenAST -> "FlattenAST"
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
  | STerm s -> (try string_of_term (get_expr t) with
               | Debug f -> s)
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

let head_term (t : term) : string = 
  match t with
  | True -> "True"
  | False -> "False"
  | Not _ -> "Not _"
  | And _ -> "And _"
  | Or _ -> "Or _"
  | Imp _ -> "Imp _"
  | Xor _ -> "Xor _"
  | Ite _ -> "Ite _"
  | Forall _ -> "Forall _"
  | Eq _ -> "Eq of _"
  | App _ -> "App _"
  | Var _ -> "Var _"
  | STerm _ -> "STerm _"
  | NTerm _ -> "NTerm _"
  | Int _ -> "Int _"
  | Lt _ -> "Lt _"
  | Leq _ -> "Leq _"
  | Gt _ -> "Gt _"
  | Geq _ -> "Geq _"
  | UMinus _ -> "UMinus _"
  | Plus _ -> "Plus _"
  | Minus _ -> "Minus _"
  | Mult _ -> "Mult _"
(* Pass through certificate, replace named terms with their
   aliases, and store the alias-term mapping in a hash table *)
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
  (* This allows equality over shared terms and other shared terms or 
     regular terms. Note that we expect perfect sharing - if the same 
     term is given 2 different names in a proof and the names are checked
     for equality, this function would return false *)
  | STerm x, s -> (match s with
                  | STerm y -> x = y
                  | t -> let x' = get_sterm x in
                         term_eq x' t)
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

let rec remove x l =
  match l with
  | h :: t -> if h = x then remove x t else h :: (remove x t)
  | [] -> []
(* Remove premise from all resolutions and transitivities in certif *)
let remove_res_trans_premise (i : id) (c : certif) : certif =
  List.map (fun s -> match s with
               | (i', r, c, p, a) when (r = ResoAST || r = ThresoAST || r = TransAST) ->
                    (i', r, c, (remove i p), a)
               | s -> s) c

let process_fins (c : certif) : certif =
  let rec process_fins_aux (c : certif) (cog : certif) : certif =
    match c with
    (* Step 1 *)
    | (i1, AnchorAST, c1, p1, a1) :: (i2, ReflAST, c2, p2, a2) ::
      (i3, CongAST, c3, p3, a3)   :: (i4, BindAST, c4, p4, a4) ::
      (i5, Equp2AST, c5, p5, a5)  :: (i6, ThresoAST, c6, p6, a6) :: t ->
        process_fins_aux (remove_res_trans_premise i6 t) cog
    (* Step 2 *)
    | (_, QcnfAST, c, _, _) :: t ->
        (* Ignoring this rule assuming no transformation is performed, 
           we need to handle this rule for more complex CNF 
           transformations of quantified formulas*)
        process_fins_aux t cog
    (* Step 3 *)
    | (i, FinsAST, c, p, a) :: tl -> 
        let st = (match (try (List.hd c) with | Failure _ -> 
                        raise (Debug ("| process_fins: clause produced by forall_inst is empty at id "^i^" |"))) with
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
(* ASSUMPTION: We assume that a ~~x is stored as just x by process_term *)
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
  | (i, NotnotAST, cl, p, a) :: tl -> process_notnot (remove_res_trans_premise i tl)
  (*| (i, NotsimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
      | [Eq (Not (Not x), y)] when x = y -> 
         (* 
            Generate x = x
            ---------eqn1  --------eqn2
            x = x, ~x      x = x, x
            -----------------------res
                     x = x   
         *)
         let eqn1i = generate_id () in
         let eqn2i = generate_id () in
         (eqn1i, Equn1AST, [Eq (x, x); Not x], [], []) :: 
         (eqn2i, Equn2AST, [Eq (x, x); x], [], []) :: 
         (i, ResoAST, [Eq (x, x)], [eqn1i; eqn2i], []) :: process_notnot (remove_res_trans_premise i tl)
      | _ -> (i, NotsimpAST, cl, p, a) :: process_notnot tl)*)
  | h :: tl -> h :: process_notnot tl
  | [] -> []



(* Remove Same rules from the certificate *)
(*
   For example, the following certificate:
     (step x ...)
     ...
     (step y ... :rule symm :premises (x))
     ...
     (step z ... :premises (y, ...))
   
   changes to:
     (step x ...)
     ...
     (step z ... :premises (x, ...)) 
   where we store symm as Same
*)
let rec replace x y l =
   match l with
   | h :: t -> if h = x then y :: replace x y t else h :: (replace x y t)
   | [] -> []
let rec replace_prem (x : id) (y : id) (c : certif) : certif =
   match c with
   | (i, r, cl, p, a) :: tl -> (i, r, cl, (replace x y p), a) :: replace_prem x y tl 
   | [] -> []
let rec process_same (c : certif) : certif =
   match c with
   | (i, SameAST, _, p, _) :: tl -> let ogi = (match p with
                                    | [p1] -> p1
                                    | _ -> raise (Debug ("| process_same : expecting a Same rule to have exactly one premise at id "^i^" |"))) in
                                    process_same (replace_prem i ogi tl)
   | h :: tl -> h :: process_same tl
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

(* term |-> bool * SmtAtom.Form.atom_form_lit |-> SmtAtom.Form.t *)

and process_term_aux (t : term) : bool * SmtAtom.Form.atom_form_lit (* option *) =
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
  | NotnotAST -> raise (Debug ("| process_rule: notnot should be eliminated|"))
  | ThresoAST -> Threso
  | ResoAST -> Reso
  | TautAST -> Taut
  | ReflAST -> Refl
  | TransAST -> raise (Debug ("| process_rule: trans should be eliminated|"))
  | CongAST -> raise (Debug ("| process_rule: cong should be eliminated|"))
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
  | ConndefAST -> raise (Debug ("| process_rule: connective_def should be eliminated|"))
  | AndsimpAST -> raise (Debug ("| process_rule: and_simplify should be eliminated|"))
  | OrsimpAST -> raise (Debug ("| process_rule: or_simplify should be eliminated|"))
  | NotsimpAST -> raise (Debug ("| process_rule: not_simplify should be eliminated|"))
  | ImpsimpAST -> raise (Debug ("| process_rule: implies_simplify should be eliminated|"))
  | EqsimpAST -> raise (Debug ("| process_rule: equiv_simplify should be eliminated|"))
  | BoolsimpAST -> raise (Debug ("| process_rule: bool_simplify should be eliminated|"))
  | AcsimpAST -> Flatten
  | ItesimpAST -> raise (Debug ("| process_rule: ite_simplify should be eliminated|"))
  | EqualsimpAST -> raise (Debug ("| process_rule: equal_simplify should be eliminated|"))
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
  | ArithpolynormAST -> Arithpolynorm
  | LiaRewriteAST -> LiaRewrite
  | BindAST -> Bind
  | FinsAST -> Fins
  | QcnfAST -> Qcnf
  | AllsimpAST -> Allsimp
  | SameAST -> Same
  | HoleAST -> Hole
  | WeakenAST -> Weaken
  | FlattenAST -> Flatten
  | AnchorAST -> Hole
  | DischargeAST -> Hole
  | SubproofAST c -> Hole



(* Removing occurrences of the cong rule using other rules 
   including eq_congruent, eq_congruent_pred, reso *)
(* This can be divided into 4 cases:
      Output         Input       Interpreted?      Encoding
      -------------------------------------------------------------------
      Bool           _           _                 Using eq_congruent_pred
      Bool           Bool        Yes               Using connective rules
      Non-bool       _           _                 Using eq_congr
   Note that even though we don't differentiate terms and formulas at the AST level,
   SMTCoq does differentiate them. This is due to veriT's previous stratification of
   terms and formulas, and complicates things for us because many of these differences
   must be inferred from the alethe certificates.
*)

(* Given a function/predicate application, for each arg, return the arg itself
   and a bool specifying whether the arg is a formula or a (non-boolean) term.
   Used to determine implicit arguments in a congruence rule application,
   and the encoding of implicit eqalities *)
let rec get_args_isfrms (t : term) : (term * bool) list =
   match get_expr t with
   | True | False | Int _ -> raise (Debug ("| get_args_isfrms : attempting congruence over constants |"))
   | Forall _ -> raise (Debug ("| get_args_isfrms : congruence over forall application unsupported |"))
   | Var _ -> raise (Debug ("| get_args_isfrms : attempting congruence over variable application |"))
   | Not x ->  [(x, true)]
   | UMinus x -> [(x, false)]
   | Plus (x, y) | Minus (x, y) | Mult (x, y) -> [(x, false); (y, false)]
   | Lt (x, y) | Leq (x, y) | Gt (x, y) | Geq (x, y) -> 
      raise (Debug ("| get_args_isfrms : congruence over integer predicates unsupported |"))
   | And xs | Or xs | Imp xs | Xor xs -> List.map (fun x -> (x, true)) xs
   | Eq (x, y) -> [(x, is_form (process_term (process_term_aux x))); (y, is_form (process_term (process_term_aux y)))]
   | Ite xs | App (_, xs) -> List.map (fun x -> (x, is_form (process_term (process_term_aux x)))) xs
   | NTerm (_, t) -> get_args_isfrms t
   | STerm s -> try get_args_isfrms (get_sterm s) with
                | Debug s -> raise (Debug ("| get_args : unable to dereference shared term |"^s))

(* returns the list of terms without (syntactic) duplicates *)
let rec to_uniq (l : 'a list) : 'a list =
   match l with
   | h :: t -> if List.exists ((=) h) t then to_uniq t else h :: to_uniq t
   | [] -> []
(*
  Example:
  1. x = y
  2. a = b
  3. f x T b = f y T a by cong(1,2)
  Given (i) the equality in the result
        (ii) the ids for the equalities in the premise
        (iii) the certificate
  Return (i) flattened list of certificates representing the steps for each implicit argument
         (ii) ordered list of (prem_id, prem_eq) pairs representing the id of the premise and 
              the equality it proves (this includes implicit and explicit premises)
*)
let cong_find_implicit_args (ft : term) (p : params) (cog : certif) : (step list * ((id * term) list)) =
   match get_expr ft with
   | Eq (fx, fy) -> let n = List.length (try get_args_isfrms fx with
                                        | Debug s -> raise (Debug ("| cong_find_implicit_args: can't get args to app |"^s))) in
                   (* no implicit equalities *)
                   if (n = List.length p) then
                     let ptuples = List.map (fun x -> (match (get_cl x cog) with
                                           (* ASSUMPTION: ideally this would be a singleton clause with the premise equality,
                                              but it could have been modified, in which case we return the first equality in the clause
                                              that we find. If clauses are modified to add more equalities before the equality that
                                              we care about, then this would fetch the wrong equality *)
                                           | Some z -> (x, try (List.find (fun y -> match (get_expr y) with
                                                                       | Eq _ -> true
                                                                       | _ -> false) z) with
                                                           | Not_found -> raise (Debug ("| cong_find_implicit_args: premise "^x^" to cong has no equalities |")))
                                           | None -> raise (Debug ("| cong_find_implicit_args: can't fetch premises to congr (no implicit equalities case) |")))) p in
                     ([], ptuples)
                   (* at least 1 implicit equality *)
                   else
                     (* Congruence over equality is a special case. Since we have to check modulo symmetry
                        the arguments may be reversed, which we don't account for in other functions. We 
                        reverse the equality here so that they can be checked pairwise *)
                     let fx', fy' = (match fx, fy with
                                     | Eq (x, y), Eq (a, b) when (x = b || y = a) -> Eq (y, x), Eq (a, b)
                                     | _, _ -> fx, fy) in
                     (* get an (argument, is_form) pair for each arg of fx and fy *)
                     let fxas_isfrms = (try get_args_isfrms fx' with
                                        | Debug s -> raise (Debug ("| cong_find_implicit_args: can't get args to app |"^s))) in
                     let fyas_isfrms = (try get_args_isfrms fy' with
                                        | Debug s -> raise (Debug ("| cong_find_implicit_args: can't get args to app |"^s))) in
                     (* get all equalities from params *)
                     let p_ids_eqs = List.map (fun x -> (match (get_cl x cog) with
                                             | Some c -> let eq = try (List.find (fun y -> match (get_expr y) with
                                                                            | Eq _ -> true
                                                                            | _ -> false) c) with
                                                                  | Not_found -> raise (Debug ("| cong_find_implicit_args: premise "^x^" to cong has no equalities |")) in
                                                         (x, eq)
                                             | None -> raise (Debug ("| cong_find_implicit_args: can't fetch premises to congr (implicit equalities case) |")))) p in
                     (* function that checks pairwise equality of arguments *)
                     let rec f (fxas_isfrms : (term * bool) list) (fyas_isfrms : (term * bool) list) (p_ids_eqs : (id * term) list) : (step list * ((id * term) list)) =
                        match fxas_isfrms, fyas_isfrms, p_ids_eqs with
                        | (fxa, fx_isfrm) :: fxat, (fya, fy_isfrm) :: fyat, (pid, Eq (px, py)) :: p_ids_eqs_t ->
                           let fxa' = get_expr fxa in
                           let fya' = get_expr fya in
                           let px' = get_expr px in
                           let py' = get_expr py in
                           (* no implicit equality *)
                           if ((fxa' = px' && fya' = py') || (fxa' = py' && fya' = px')) then
                              let (imp, ptuples) = f fxat fyat p_ids_eqs_t in
                              (imp, (pid, (Eq (px', py'))) :: ptuples)
                           (* implicit equality found *)
                           else if (fxa' = fya') then
                              let (imp, ptuples) = f fxat fyat ((pid, Eq (px', py')) :: p_ids_eqs_t) in
                              let impi = generate_id () in
                              let cert = (if fx_isfrm then
                                           let eqn1i = generate_id () in
                                           let eqn2i = generate_id () in
                                           (eqn1i, Equn1AST, [Eq (fxa', fya'); fxa'], [], []) ::
                                           (eqn2i, Equn2AST, [Eq (fxa', fya'); Not fxa'], [], []) ::
                                           (impi, ResoAST, [Eq (fxa', fya')], [eqn1i; eqn2i], []) :: imp
                                         else
                                           (impi, ReflAST, [Eq (fxa', fya')], [], []) :: imp) in
                              (cert, (impi, Eq (fxa', fya')) :: ptuples)
                           else
                              raise (Debug ("| cong_find_implicit_args.f: can't find implicit premise to congr |"))
                        (* implicit equalities at the end *)
                        | (fxa, fx_isfrm) :: fxat, (fya, fy_isfrm) :: fyat, [] ->
                           let fxa' = get_expr fxa in
                           let fya' = get_expr fya in
                           if (fxa' = fya') then
                              let (imp, ptuples) = f fxat fyat [] in
                              let impi = generate_id () in
                              let cert = (if fx_isfrm then
                                           let eqn1i = generate_id () in
                                           let eqn2i = generate_id () in
                                           (eqn1i, Equn1AST, [Eq (fxa', fya'); fxa'], [], []) ::
                                           (eqn2i, Equn2AST, [Eq (fxa', fya'); Not fxa'], [], []) ::
                                           (impi, ResoAST, [Eq (fxa', fya')], [eqn1i; eqn2i], []) :: imp
                                         else
                                           (impi, ReflAST, [Eq (fxa', fya')], [], []) :: imp) in
                              (cert, (impi, Eq (fxa', fya')) :: ptuples)
                           else
                              raise (Debug ("| cong_find_implicit_args.f: can't find implicit premise to congr |"))
                        | [], [] ,[] -> ([], [])
                        | _ -> raise (Debug ("| cong_find_implicit_args.f: number of arguments don't match with premises |"))
                     in f fxas_isfrms fyas_isfrms p_ids_eqs
   | _ -> raise (Debug ("| cong_find_implicit_args: expecting head of clause to be an equality |"))

let process_cong (c : certif) : certif =
  let rec process_cong_aux (c : certif) (cog : certif) : certif = 
   match c with
    | (i, CongAST, cl, p, a) :: t ->
        (* To differentiate between the predicate and function case, we need to process
           the clause because we treat equality and iff as the same at the AST level *)
        let c' = try process_cl cl with
                 | Form.NotWellTyped frm -> raise (Debug ("| process_cong: formula "^
                 (Form.pform_to_string frm)^" is not well-typed at id "^i^" |")) in
        (match c' with
          | l :: _ ->
            (match cl with
              (* 1. Congruence over equality:
                    x = a   y = b
                  -----------------cong
                  (x = y) = (a = b) *)
              | Eq (Eq (x, y), Eq (a, b)) as eq :: _ -> 
                   (* Are x, y, a, b (non-bool) terms or (bool) formulas? *)
                   let is_frm = try (
                      match Form.pform l with
                      | Fapp (Fiff, args) -> (match Form.pform (Array.get args 0), Form.pform (Array.get args 1) with
                                              | Fapp (Fiff, args0), Fapp (Fiff, args1) -> 
                                                  is_form (Array.get args0 0) && is_form (Array.get args0 1)
                                              | _, _ -> false)
                      | _ -> false
                    ) with
                    | Form.NotWellTyped frm -> raise (Debug ("| process_cong: formula "^
                         (Form.pform_to_string frm)^" is not well-typed at id "^i^" |")) in
                   (* Find any implicit premises *)
                   (* imp will store the steps for the implicit premise, if any;
                      pids is a list of ids of all the premises including implicit ones;
                      prem_negs is a list of the negatations of all premises *)
                    let imp, pids, prem_negs =
                    (match p with
                    | [p'] -> 
                       let p1, p2 = 
                          match get_cl p' cog with
                          | Some (Eq (x, a) :: _) -> (x, a)
                          | _ -> raise (Debug ("| process_cong: expecting premise of cong to be an equality |")) in
                       let impi = generate_id () in
                       (* find implicit premise modulo symmetry *)
                       let q1, q2, ps = 
                          if      (p1 = x && p2 = a) || (p1 = a && p2 = x) then (y, b, [p'; impi])
                          else if (p1 = x && p2 = b) || (p1 = b && p2 = x) then (y, a, [p'; impi])
                          else if (p1 = y && p2 = a) || (p1 = a && p2 = y) then (x, b, [impi; p'])
                          else if (p1 = y && p2 = b) || (p1 = b && p2 = y) then (x, a, [impi; p'])
                          else raise (Debug ("| process_cong: can't find implicit premise for cong over eq |")) in
                       let cert = if is_frm then
                                    let eqn1i = generate_id () in
                                    let eqn2i = generate_id () in
                                    [(eqn1i, Equn1AST, [Eq (q1, q2); q1], [], []);
                                     (eqn2i, Equn2AST, [Eq (q1, q2); Not q2], [], []);
                                     (impi, ResoAST, [Eq (q1, q2)], [eqn1i; eqn2i], [])]
                                  else
                                    [(impi, ReflAST, [Eq (q1, q2)], [], [])] in
                       (cert, 
                        ps, 
                        [Not (Eq (q1, q2)); Not (Eq (p1, p2))])
                    | [_; _] ->
                       let prem_negs' = 
                        List.map (fun x -> (match get_cl x cog with
                           (* ASSUMPTION: ideally this would be a singleton clause with the premise equality,
                              but it could have been modified, in which case we return the first equality in the clause
                              that we find. If clauses are modified to add more equalities before the equality that
                              we care about, then this would fetch the wrong equality *)
                          | Some z -> (try Not (List.find (fun y -> match (get_expr y) with
                                                   | Eq _ -> true
                                                   | _ -> false) z) with
                                      | Not_found -> raise (Debug ("| process_cong: premise "^x^" to cong has no equalities |")))
                          | None -> raise (Debug ("| process_cong: can't fetch premises to congr (no implicit equalities case) |")))) p in
                       ([], 
                        p,
                        prem_negs')
                    | _ -> raise (Debug ("| process_cong: cong has 0 or > 2 premises at id "^i^" |"))) in
                    (* x, y, a, b are (non-bool) terms *)
                    if (not is_frm) then
                      (*
                        Convert a proof of the form:
                        -----       -----
                        x = a       y = b
                        -----------------cong
                        (x = y) = (a = b)
                        to:
                              (1)                      (2)                 (3)                     (4)
                        ----------------------------------------res  -----------------------------------------res  -----    -----
                        x != a, y != b, a = b, (x = y) = (a = b)     x != a, y != b, a != b, (x = y) = (a = b)     x = a    y = b
                        ---------------------------------------------------------------------------------------------------------res
                                                                     (x = y) = (a = b)
                        where:
                        -----------------------------eqtrans
                        x != a, y != b, x != y, a = b       --(1)
                        -------------------------------eqn2
                        (x = y) = (a = b), x = y, a = b     --(2)
                        -----------------------------eqtrans
                        x != a, y != b, a != b, x = y       --(3)
                        ---------------------------------eqn1
                        (x = y) = (a = b), x != y, a != b   --(4) 
                      *)
                        let eqcpi1 = generate_id () in
                        let eqcpi2 = generate_id () in
                        let eqn2i = generate_id () in
                        let eqn1i = generate_id () in
                        let resi1 = generate_id () in
                        let resi2 = generate_id () in
                        let xy = Eq (x, y) in
                        let ab = Eq (a, b) in
                          imp @
                          ((eqcpi1, EqtrAST, (prem_negs @ [Not xy; ab]), [], []) ::
                           (eqn2i, Equn2AST, [eq; xy; ab], [], []) ::
                           (resi1, ResoAST, (prem_negs @ [ab; eq]), [eqcpi1; eqn2i], []) ::
                           (eqcpi2, EqtrAST, (prem_negs @ [Not ab; xy]), [], []) ::
                           (eqn1i, Equn1AST, [eq; Not xy; Not ab], [], []) ::
                           (resi2, ResoAST, (prem_negs @ [Not ab; eq]), [eqcpi2; eqn1i], []) ::
                           (i, ResoAST, [eq], resi1 :: resi2 :: pids, []) ::
                           process_cong_aux t cog)
                    (* x, y, a, b are (bool) formulas *)
                    else
                    (* iff predicate
                        -----  ---------------eqp1                                                                             
                        y = b  ~(y = b), y, ~b                                                                                 
                        ----------------------res  ----------------eqp1  -----------eqn2  -------------------------------eqn2  
                                y, ~b              ~(x = y),  x, ~y      a = b, a, b      (x = y) = (a = b), x = y, a = b      
                                -----------------------------------------------------------------------------------------res   
                                                                (x = y) = (a = b), a = b, x, a --(1)                           

                                                        -----  ---------------eqp2
                                                        y = b  ~(y = b), ~y, b
                                                        ----------------------res  -----------eqn2  --------------eqp1  -------------------------------------eqn1  -----  ---------------eqp1
                                                                ~y, b              x = y, x, y      ~(a = b), a ~b      (x = y) = (a = b), ~(x = y), ~(a = b)      x = a  ~(x = a), x, ~a
                        ------------------------------(1)       ---------------------------------------------------------------------------------------------res   ----------------------res 
                        (x = y) = (a = b), a = b, x, a                                           (x = y) = (a = b), ~(a = b), x, a                                          x, ~a
                        ---------------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                         (x = y) = (a = b), x --(2)

                        -----  ---------------eqp2
                        x = a  ~(x = a), ~x, a
                        ----------------------res  --------------------(2)
                                ~x, a              (x = y) = (a = b), x
                                ---------------------------------------                                                                                                             
                                         (x = y) = (a = b), a --(3)

                                                                                                         -----  ---------------eqp2
                                                                                                         y = b  ~(y = b), ~y, b
                        -------------------------------------eqn1  -------------eqn1  -------------eqn1  ----------------------res  --------------------(3)  --------------------(2)  -----  ---------------eqp1
                        (x = y) = (a = b), ~(x = y), ~(a = b)      a = b, ~a, ~b      x = y, ~x, ~y              ~y, b              (x = y) = (a = b), a     (x = y) = (a = b), x     y = b  ~(y = b), y, ~b
                        ---------------------------------------------------------------------------------------------------------------------------------------------------------res  ----------------------res 
                                                                                              (x = y) = (a = b), ~y --(4)                                                                       y, ~b
                                                                                              -----------------------------------------------------------------------------------------------------res
                                                                                                                                        (x = y) = (a = b), ~b --(5)

                                                             ---------------eqp2  ---------------------(4)  --------------------(2)  ---------------eqp2  ---------------------(5)  --------------------(3)
                                                             ~(x = y), ~x, y      (x = y) = (a = b), ~y     (x = y) = (a = b), x     ~(a = b), ~a, b      (x = y) = (a = b), ~b     (x = y) = (a = b), a
                        -------------------------------eqn2  -------------------------------------------------------------------res  -------------------------------------------------------------------res
                        (x = y) = (a = b), x = y, a = b                       (x = y) = (a = b), ~(x = y)                                               (x = y) = (a = b), ~(a = b)
                        -----------------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                               (x = y) = (a = b)
                     *)
                       (* Get premise ids *)
                       let p1 = List.nth pids 0 in
                       let p2 = List.nth pids 1 in
                       (* Given (x = y) = (a = b) in the conclusion, *)
                       (* 1. Generate ~(y = b), y, ~b by eqp1 and resolve it with y = b to get y, ~b *)
                       let ynotb, ynotbi = 
                        if y = b then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i1 = generate_id () in
                          let resi1 = generate_id () in
                          ([(eqp1i1, Equp1AST, [Not (Eq (y, b)); y; Not b], [], []);
                            (resi1, ResoAST, [y; Not b], [p2; eqp1i1], [])], 
                           [resi1]) in
                       (* 2. Generate ~(x = y),  x, ~y by eqp1, a = b, a, b by eqn2, (x = y) = (a = b), x = y, a = b by eqn2 and resolve all of them with 1. to get (x = y) = (a = b), a = b, x, a *)
                       let eqp1i2 = generate_id () in
                       let eqn2i1 = generate_id () in
                       let eqn2i2 = generate_id () in
                       let resi2 = generate_id () in
                       (* 3. Generate ~(y = b), ~y, b by eqp2, and resolve it with y = b to get ~y, b *)
                       let notyb, notybi =
                        if y = b then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp2i1 = generate_id () in
                          let resi3 = generate_id () in
                          ([(eqp2i1, Equp2AST, [Not (Eq (y, b)); Not y; b], [], []);
                            (resi3, ResoAST, [Not y; b], [p2; eqp2i1], [])], 
                           [resi3]) in
                       (* 4. Generate x = y, x, y by eqn2, ~(a = b), a ~b by eqp1, (x = y) = (a = b), ~(x = y), ~(a = b) by eqn1, and resolve all of them with 3. to get (x = y) = (a = b), ~(a = b), x, a *)
                       let eqn2i3 = generate_id () in
                       let eqp1i3 = generate_id () in
                       let eqn1i1 = generate_id () in
                       let resi4 = generate_id () in
                       (* 5. Generate ~(x = a), x, ~a by eqp1 and resolve it with x = a to get x, ~a *)
                       let xnota, xnotai =
                        if x = a then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i4 = generate_id () in
                          let resi5 = generate_id () in
                          ([(eqp1i4, Equp1AST, [Not (Eq (x, a)); x; Not a], [], []);
                            (resi5, ResoAST, [x; Not a], [p1; eqp1i4], [])],
                           [resi5]) in
                       (* 6. Resolve 2., 4., and 5. to get (x = y) = (a = b), x *)
                       let resi6 = generate_id () in
                       (* 7. Generate ~(x = a), ~x, a by eqp2 and resolve with x = a to get ~x, a *)
                       let notxa, notxai =
                        if x = a then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp2i2 = generate_id () in
                          let resi7 = generate_id () in
                          ([(eqp2i2, Equp2AST, [Not (Eq (x, a)); Not x; a], [], []);
                            (resi7, ResoAST, [Not x; a], [p1; eqp2i2], [])],
                           [resi7]) in
                       (* 8. Resolve 6. and 7. to get (x = y) = (a = b), a *)
                       let eqa, eqai1, eqai2 = 
                        if x = a then [], [], resi6 (* this derivation is unnecessary and unsound for refl equality, except in one place where it is replaced by derivation resi6 *)
                        else
                          let resi8 = generate_id () in
                          (notxa @                       
                           [(resi8, ResoAST, [eq; a], resi6 :: notxai, [])],
                           [resi8],
                           resi8) in
                       (* 9. Resolve (x = y) = (a = b), ~(x = y), ~(a = b) by eqn1 (reuse from 4.), a = b, ~a, ~b by eqn1, x = y, ~x, ~y by eqn1, 3., 8., and 6. to get (x = y) = (a = b), ~y *)
                       let eqn1i2 = generate_id () in
                       let eqn1i3 = generate_id () in
                       let resi9 = generate_id () in
                       (* 10. Resolve 9. and 1. to get (x = y) = (a = b), ~b *)
                       let resi10 = generate_id () in
                       (* 11. Resolve ~(x = y), ~x, y by eqp2, 9., and 6. to get  (x = y) = (a = b), ~(x = y) *)
                       let eqp2i3 = generate_id () in
                       let resi11 = generate_id () in
                       (* 12. Resolve ~(a = b), ~a, b by eqp2, 10., and 8. to get (x = y) = (a = b), ~(a = b) *)
                       let eqp2i4 = generate_id () in
                       let resi12 = generate_id () in
                       imp @ ynotb @
                       (eqp1i2, Equp1AST, [Not (Eq (x, y)); x; Not y], [], []) ::
                       (eqn2i1, Equn2AST, [Eq (a, b); a; b],[], []) ::
                       (eqn2i2, Equn2AST, [eq; Eq (x, y); Eq (a, b)], [], []) ::
                       (resi2, ResoAST, [eq; Eq (a, b); x; a], ynotbi @ [eqp1i2; eqn2i1; eqn2i2], []) :: notyb @
                       (eqn2i3, Equn2AST, [Eq (x, y); x; y], [], []) ::
                       (eqp1i3, Equp1AST, [Not (Eq (a, b)); a; Not b], [], []) ::
                       (eqn1i1, Equn1AST, [eq; Not (Eq (x, y)); Not (Eq (a, b))], [], []) ::
                       (resi4, ResoAST, [eq; Not (Eq (a, b)); x; a], notybi @ [eqn2i3; eqp1i3; eqn1i1], []) :: xnota @
                       (resi6, ResoAST, [eq; x], [resi2; resi4] @ xnotai, []) :: 
                       (eqn1i2, Equn1AST, [Eq (a, b); Not a; Not b], [], []) ::
                       (eqn1i3, Equn1AST, [Eq (x, y); Not x; Not y], [], []) :: eqa @
                       (resi9, ResoAST, [eq; Not y], [eqn1i1; eqn1i2; eqn1i3] @ notybi @ eqai1 @ [resi6], []) ::
                       (resi10, ResoAST, [eq; Not b], resi9 :: ynotbi, []) ::
                       (eqp2i3, Equp2AST, [Not (Eq (x, y)); Not x; y], [], []) ::
                       (resi11, ResoAST, [eq; Not (Eq (x, y))], [eqp2i3; resi9; resi6], []) ::
                       (eqp2i4, Equp2AST, [Not (Eq (a, b)); Not a; b], [], []) ::
                       (resi12, ResoAST, [eq; Not (Eq (a, b))], [eqp2i4; resi10; eqai2], []) ::
                       (* 13. Generate (x = y) = (a = b), x = y, a = b (reuse from 2.) by eqn2 and resolve it with 11. and 12. to get (x = y) = (a = b) *)
                       (i, ResoAST, [eq], [eqn2i2; resi11; resi12], []) ::
                       process_cong_aux t cog
              | _ ->
                let conc = get_expr (try (List.hd cl) with | Failure _ -> 
                                     raise (Debug ("| process_cong: clause produced by cong is empty at id "^i^" |"))) in
                (* 2. Congruence over functions *)
                if is_eq l then
                  (*
                     Convert a proof of the form:
                     ...
                     x = a              y = b
                     ------------------------cong
                         f(x, y) = f(a, b)

                     to:
                     ...
                     -------------------------------------eqcong
                     ~(x = a), ~(y = b), (f(x,y) = f(a,b))          x = a    y = b
                     --------------------------------------------------------------res
                                           f(x,y) = f(a,b)   
                  *)
                  let imp, ptuples = try (cong_find_implicit_args conc p cog) with 
                                     | Debug s -> raise (Debug ("| process_cong: can't find premise(s) to congr at id "^i^" |"^s)) in
                  let pids, peqs = List.split ptuples in
                  let prem_negs = List.map (fun x -> Not x) peqs in
                  let eqci = generate_id () in
                    imp @
                    ((eqci, EqcoAST, (prem_negs @ cl), [], []) ::
                     (i, ResoAST, cl, eqci :: pids, a) :: 
                     process_cong_aux t cog)
                (* 3. Congruence over predicates *)
                (* ASSUMPTION: we're assuming that x = a is the first premise and y = b 
                          the second premise to congruence *)
                else if is_iff l then
                  let imp, ptuples = try (cong_find_implicit_args conc p cog) with 
                                     | Debug s -> raise (Debug ("| process_cong: can't find premise(s) to congr at id "^i^" |"^s)) in
                  let pids, peqs = List.split ptuples in
                  let prem_negs = List.map (fun x -> Not x) peqs in
                  let eq = (try (List.hd cl) with | Failure _ -> 
                            raise (Debug ("| process_cong: clause produced by cong is empty at id "^i^" |"))) in
                     (match (get_expr eq) with
                     (* and predicate
                        Convert a proof of the form:
                         -----  -----
                         x = a  y = b
                        --------------cong
                         x ^ y = a ^ b 

                        to one of the form:
                        (1)       (2)
                        -------------res
                        x ^ y = a ^ b
                        where (1) and (2) are derived as:
                                             -----   ---------------eqp1                   -----   -----------------eqp1
                                             x = a   ~(x = a), x, ~a                       y = b   ~(y = b), y, ~b
                                             ----------------------res   ------------andp  -------------------------res  ------------andp
                                                    ~a, x                ~(a ^ b), a                ~b, y                ~(a ^ b), b
                        ---------------andn         --------------------------------res             --------------------------------res
                        (x ^ y), ~x, ~y                    ~(a ^ b), x                                           ~(a ^ b), y
                        ----------------------------------------------------------------------------------------------------res  ---------------------------------eqn2
                                                                  ~(a ^ b), (x ^ y)                                              x ^ y = a ^ b, (x ^ y), (a ^ b)     
                                                                  ----------------------------------------------------------------------------------------------res
                                                                                                  x ^ y = a ^ b, (x ^ y) --(1)

                                             -----   ---------------eqp2                  -----   -----------------eqp2
                                             x = a   ~(x = a), ~x, a                      y = b    ~(y = b), ~y, b
                                             -----------------------res  -----------andp  ------------------------res  -----------andp
                                                      ~x, a              ~(x ^ y), x               ~y, b               ~(x ^ y), y
                        ---------------andn           ------------------------------res            -------------------------------res
                        (a ^ b), ~a, ~b                         ~(x ^ y), a                                  ~(x ^ y), b
                        ------------------------------------------------------------------------------------------------res  ---------------------------------eqn1
                                                                    ~(x ^ y), (a ^ b)                                        x ^ y = a ^ b, ~(x ^ y), ~(a ^ b)
                                                                    ------------------------------------------------------------------------------------------res
                                                                                                  x ^ y = a ^ b, ~(x ^ y) --(2)
                         Under both trees, if a premise is a reflexivity, then the derivation from it using eqp1/2, andp and res must be shortened just to an andp
                     *)
                     | Eq (And xs, And ys) ->
                        (* For x1 ^ ... ^ xn = y1 ^ ... ^ ym in the conclusion, *)
                        (* 1. generate x1 ^ ... ^ xn, ~x1, ..., ~xn by andn *)
                        let andni1 = generate_id () in
                        let andns1 = List.map (fun x -> Not x) xs in
                        (* 2. for each non-refl equality x = y in premise, (for refl equalities, simply generate step (iv) by andp)
                              (i) generate ~(x = y), x, ~y by eqp1
                              (ii) resolve it with x = y, to get ~y, x
                              (iii) generate ~(y1 ^ ... ^ ym), y by andp
                              (iv) resolve (ii) and (iii) to get ~(y1 ^ ... ^ ym), x *)
                        let resi1s, res1s = List.fold_left 
                          (fun (ris, rs) (pid, peq) ->
                            let x, y = (match (get_expr peq) with
                                        | Eq (x', y') -> (x', y')
                                        | _ -> raise (Debug ("| process_cong: expecting premise of cong to be equality at id "^i^" instead I have "^(head_term (get_expr peq))^" |"))) in
                            if x = y then
                              let andpi = generate_id () in
                              let ind = string_of_int (findi (term_eq x) ys) in
                              (andpi :: ris, 
                               (andpi, AndpAST, [Not (And ys); x], [], [ind]) :: rs)
                            else
                              let eqp1i = generate_id () in
                              let resi1 = generate_id () in
                              let andpi = generate_id () in
                              let resi2 = generate_id () in
                              let ind = string_of_int (findi (term_eq y) ys) in
                              (resi2 :: ris, 
                               (eqp1i, Equp1AST, [Not peq; x; Not y], [], []) :: 
                               (resi1, ResoAST, [x; Not y], [eqp1i; pid], []) :: 
                               (andpi, AndpAST, [Not (And ys); y], [], [ind]) ::
                               (resi2, ResoAST, [Not (And ys); x], [resi1; andpi], []) :: rs))
                          ([], []) ptuples in
                        (* 3. resolve all clauses form 1. and 2. to get ~(y1 ^ ... ^ ym), x1 ^ ... ^ xn *)
                        let resi1 = generate_id () in
                        (* 4. generate x1 ^ ... ^ xn = y1 ^ ... ^ ym, x1 ^ ... ^ xn, y1 ^ ... ^ ym by eqn2 *)
                        let eqn2i = generate_id () in
                        (* 5. resolve 3. and 4. to get x1 ^ ... ^ xn = y1 ^ ... ^ ym, x1 ^ ... ^ xn *)
                        let resi2 = generate_id () in
                        (* 6. generate y1 ^ ... ^ ym, ~y1, ..., ~ym by andn *)
                        let andni2 = generate_id () in
                        let andns2 = List.map (fun x -> Not x) ys in
                        (* 7. for each non-refl equality x = y in premise, (for refl equalities, simply generate step (iv) by andp)
                              (i) generate ~(x = y), ~x, y by eqp2
                              (ii) resolve it with x = y, to get y, ~x
                              (iii) generate ~(x1 ^ ... ^ xn), x by andp
                              (iv) resolve (ii) and (iii) to get ~(x1 ^ ... ^ xn), y *)
                        let resi2s, res2s = List.fold_left
                          (fun (ris, rs) (pid, peq) ->
                            let x, y = (match (get_expr peq) with
                                        | Eq (x', y') -> (x', y')
                                        | _ -> raise (Debug ("| process_cong: expecting premise of cong to be equality at id "^i^" |"))) in
                            if x = y then
                               let andpi = generate_id () in
                               let ind = string_of_int (findi (term_eq y) xs) in
                               (andpi :: ris,
                                (andpi, AndpAST, [Not (And xs); y], [], [ind]) :: rs)
                            else
                              let eqp2i = generate_id () in
                              let resi1 = generate_id () in
                              let andpi = generate_id () in
                              let resi2 = generate_id () in
                              let ind = string_of_int (findi (term_eq x) xs) in
                              (resi2 :: ris, 
                               (eqp2i, Equp2AST, [Not peq; Not x; y], [], []) :: 
                               (resi1, ResoAST, [Not x; y], [eqp2i; pid], []) :: 
                               (andpi, AndpAST, [Not (And xs); x], [], [ind]) ::
                               (resi2, ResoAST, [Not (And xs); y], [resi1; andpi], []) :: rs))
                          ([], []) ptuples in
                        (* 8. resolve all clauses form 6. and 7. to get ~(x1 ^ ... ^ xn), y1 ^ ... ^ ym *)
                        let resi3 = generate_id () in
                        (* 9. generate x1 ^ ... ^ xn = y1 ^ ... ^ ym, ~(x1 ^ ... ^ xn), ~(y1 ^ ... ^ ym) by eqn1 *)
                        let eqn1i = generate_id () in
                        (* 10. resolve 8. and 9. to get x1 ^ ... ^ xn = y1 ^ ... ^ ym, ~(x1 ^ ... ^ xn) *)
                        let resi4 = generate_id () in
                        imp @
                        ((andni1, AndnAST, (And xs :: andns1), [], []) :: res1s) @
                        ((resi1, ResoAST, [Not (And ys); And xs], (andni1 :: resi1s), []) ::
                         (eqn2i, Equn2AST, [eq; And xs; And ys], [], []) ::
                         (resi2, ResoAST, [eq; And xs], [resi1; eqn2i], []) ::
                         (andni2, AndnAST, (And ys :: andns2), [], []) :: res2s) @
                        ((resi3, ResoAST, [Not (And xs); And ys], (andni2 :: resi2s), []) ::
                         (eqn1i, Equn1AST, [eq; Not (And xs); Not (And ys)], [], []) ::
                         (resi4, ResoAST, [eq; Not (And xs)], [resi3; eqn1i], []) ::
                         (* 11. resolve 5. and 10. to get x1 ^ ... ^ xn = y1 ^ ... ^ ym    *)
                         (i, ResoAST, [eq], [resi2; resi4], []) ::
                         process_cong_aux t cog)
                     (* or predicate
                        Convert a proof of the form:
                         -----  -----
                         x = a  y = b
                        --------------cong
                         x v y = a v b

                        to one of the form:
                        (1)       (2)
                        -------------res
                        x v y = a v b
                        where (1) and (2) are derived as:
                                            -----   ---------------eqp2  -----   -----------------eqp2                                                                          
                                            x = a   ~(x = a), ~x, a      y = b    ~(y = b), ~y, b                                                                               
                        ---------------orp  ----------------------res   -------------------------res  ------------orn    ------------orn                                        
                        ~(x v y), x, y             ~x, a                         ~y, b                (a v b), ~a         (a v b), ~b                                           
                        --------------------------------------------------------------------------------------------------------------res  ---------------------------------eqn2
                                                                    ~(x v y), (a v b)                                                       x v y = a v b, (x v y), (a v b)     
                                              -----------------------------------------------------------------------------------------------------------------------------res  
                                                                                        x v y = a v b, (a v b) --(1)

                                              -----  ---------------eqp1  -----  -----------------eqp1 
                                              x = a  ~(x = a), ~a, x      y = b  ~(y = b), ~b, y       
                        ---------------orp  -----------------------res   ------------------------res  -----------orn  -----------orn
                        ~(a v b), a, b               ~a, x                       ~b, y                (x v y), ~x     (x v y), ~y
                        ---------------------------------------------------------------------------------------------------------res  ---------------------------------eqn1
                                                                          ~(a v b), (x v y)                                            x v y = a v b, ~(x v y), ~(a v b)
                                                                          ---------------------------------------------------------------------------------------------res
                                                                                                              x v y = a v b, ~(a v b) --(2)
                     *)
                     | Eq (Or xs, Or ys) ->
                        (* For `x1 v ... v xn = y1 v ... v ym` in the conclusion, *)
                        (* 1. generate `~(x1 v ... v xn), x1, ..., xn` by `orp` *)
                        let orpi1 = generate_id () in
                        (* 2. for each non-refl equality `x = y` in premise, generate `~(x = y), y, ~x` by `eqp2` 
                              and resolve it with `x = y`, to get `y, ~x` *)
                        let eqp2is, eqp2s = List.fold_left 
                          (fun (is, r) (pid, peq) ->
                            let x, y = (match (get_expr peq) with
                                        | Eq (x', y') -> (x', y')
                                        | _ -> raise (Debug ("| process_cong: expecting premise of cong to be equality at id "^i^" |"))) in
                            if x = y then (is, r)
                            else
                             let i' = generate_id () in
                             let eqp2i = generate_id () in
                             (i' :: is, 
                              (eqp2i, Equp2AST, [Not peq; Not x; y], [], []) :: 
                              (i', ResoAST, [Not x; y], [eqp2i; pid], []) :: r))
                          ([], []) ptuples in
                        (* 3. for each `yi`, generate `(y1 v ... v ym), ~yi` by `orn` *)
                        let ornis1, orns1 = List.fold_left
                          (fun (is, r) y ->
                            let i' = generate_id () in
                            let proj = try findi (term_eq y) ys with
                                        | Debug s -> raise (Debug ("| process_cong: fails at id "^i^" |"^s)) in
                            i' :: is,
                            (i', OrnAST, [Or ys; Not y], [], [string_of_int proj]) :: r)
                          ([], []) (to_uniq ys) in
                        (* 4. resolve all clauses form 1., 2., and 3., to get `~(x1 v ... v xn), y1 v ... v ym` *)
                        let resi1 = generate_id () in
                        (* 5. generate `x1 v ... v xn = y1 v ... v ym, x1 v ... v xn, y1 v ... v ym` by `eqn2` *)
                        let eqn2i = generate_id () in
                        (* 6. resolve 4. and 5. to get `x1 v ... v xn = y1 v ... v ym, y1 v ... v ym` *)
                        let resi2 = generate_id () in
                        (* 7. generate `~(y1 v ... v ym), y1, ..., ym` by `orp` *)
                        let orpi2 = generate_id () in
                        (* 8. for each non-refl equality `x = y` in premise, generate `~(x = y), ~y, x` by `eqp1`
                              and resolve it with `x = y`, to get `~y, x` *)
                        let eqp1is, eqp1s = List.fold_left
                          (fun (is, r) (pid, peq) ->
                            let x, y = (match (get_expr peq) with
                                        | Eq (x', y') -> (x', y')
                                        | _ -> raise (Debug ("| process_cong: expecting premise of cong to be equality at id "^i^" |"))) in
                            if x = y then (is, r)
                            else
                             let i' = generate_id () in
                             let eqp1i = generate_id () in
                             (i' :: is, 
                              (eqp1i, Equp1AST, [Not peq; x; Not y], [], []) :: 
                              (i', ResoAST, [x; Not y], [eqp1i; pid], []) :: r))
                          ([], []) ptuples in
                        (* 9. for each `xi`, generate `(x1 v ... v xn), ~xi` by `orn` *)
                        let ornis2, orns2 = List.fold_left
                          (fun (is, r) x ->
                            let i' = generate_id () in
                            let proj = try findi (term_eq x) xs with
                                        | Debug s -> raise (Debug ("| process_cong: fails at id "^i^" |"^s)) in
                            i' :: is,
                            (i', OrnAST, [Or xs; Not x], [], [string_of_int proj]) :: r)
                          ([], []) (to_uniq xs) in
                        (* 10. resolve all clauses form 7., 8., and 9., to get `~(y1 v ... v ym), x1 v ... v xn` *)
                        let resi3 = generate_id () in
                        (* 11. generate `x1 v ... v xn = y1 v ... v ym, ~(x1 v ... v xn), ~(y1 v ... v ym)` by `eqn1` *)
                        let eqn1i = generate_id () in
                        (* 12. resolve 10. and 11. to get `x1 v ... v xn = y1 v ... v ym, ~(y1 v ... v ym)` *)
                        let resi4 = generate_id () in
                        imp @
                        ((orpi1, OrpAST, (Not (Or xs) :: xs), [], []) ::
                         (eqp2s @ orns1)) @
                        ((resi1, ResoAST, [Not (Or xs); Or ys], (orpi1 :: (eqp2is @ ornis1)), []) ::
                         (eqn2i, Equn2AST, [eq; Or xs; Or ys], [], []) ::
                         (resi2, ResoAST, [eq; Or xs], [resi1; eqn2i], []) ::
                         (orpi2, OrpAST, (Not (Or ys) :: ys), [], []) ::
                         (eqp1s @ orns2)) @
                        ((resi3, ResoAST, [Not (Or ys); Or xs], (orpi2 :: (eqp1is @ ornis2)), []) ::
                         (eqn1i, Equn1AST, [eq; Not (Or xs); Not (Or ys)], [], []) ::
                         (resi4, ResoAST, [eq; Not (Or ys)], [resi3; eqn1i], []) ::
                         (* 13. resolve 6. and 12. to get `x1 v ... v xn = y1 v ... v ym` *)
                         (i, ResoAST, [eq], [resi2; resi4], []) ::
                         process_cong_aux t cog)
                     (* imp predicate
                        Convert a proof of the form:
                        -----  -----
                        x = a  y = b
                        --------------cong
                        x -> y = a -> b

                        to one of the form:
                              -------------------------------eqn2       -------------------------------------eqn1
                        (1)   x -> y = a -> b, x -> y, a -> b      (2)  x -> y = a -> b, ~(x -> y), ~(a -> b)
                        -------------------------------------res   ------------------------------------------res
                               x -> y = a -> b, x -> y                     x -> y = a -> b, ~(x -> y)
                               ----------------------------------------------------------------------res
                                                         x -> y = a -> b
                        where (1) and (2) are derived as:
                                              -----   ---------------eqp2  -----  -----------------eqp1
                                              x = a   ~(x = a), ~x, a      y = b  ~(y = b), y, ~b      
                        ----------------impp  ------------------------res  ------------------------res 
                        ~(a -> b), ~a, b               ~x, a                        y, ~b              
                        -----------------------------------------------------------------res  ---------impn1  ----------impn2
                                                ~(a -> b), ~x, y                              x -> y, x       x -> y, ~y
                                                ------------------------------------------------------------------------res  
                                                                        ~(a -> b), x -> y  ---(1)                            

                                              -----   -----------------eqp2  -----  ---------------eqp1
                                              y = b    ~(y = b), ~y, b       x = a  ~(x = a), x, ~a    
                        ----------------impp  -------------------------res   -----------------------res
                        ~(x -> y), ~x, y                ~y, b                         x, ~a
                        -------------------------------------------------------------------res  ---------impn1  ----------impn2
                                                ~(x -> y), b, ~a                                a -> b, a       a -> b, ~b
                                                --------------------------------------------------------------------------res  
                                                                        ~(x -> y), a -> b  ---(2)
                     *)
                     | Eq (Imp [x; y], Imp [a; b]) ->
                       let xy = Imp [x; y] in
                       let ab = Imp [a; b] in
                       let eqxa = Eq (x, a) in
                       let eqyb = Eq (y, b) in
                       (* Get premise ids *)
                       let p1 = (match (List.nth ptuples 0) with
                                 | (pid, _) -> pid) in
                       let p2 = (match (List.nth ptuples 1) with
                                 | (pid, _) -> pid) in
                       (* Given `x -> y = a -> b` in the conclusion, *)
                       (* 1. generate `~(x -> y), ~x, y` by `impp` *)
                       let imppi1 = generate_id () in
                       (* 2. generate `~(y = b), ~y, b` by `eqp2` and resolve it with premise `y = b` to get `~y, b` *)
                       let notyb, notybi =
                        if y = b then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp2i1 = generate_id () in
                          let resi1 = generate_id () in
                          ([(eqp2i1, Equp2AST, [Not eqyb; Not y; b], [], []);
                            (resi1, ResoAST, [Not y; b], [eqp2i1; p2], [])],
                           [resi1]) in
                       (* 3. generate `~(x = a), ~a, x` by `eqp1` and resolve it with premise `x = a` to get `x, ~a` *)
                       let xnota, xnotai =
                        if x = a then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i1 = generate_id () in
                          let resi2 = generate_id () in
                          ([(eqp1i1, Equp1AST, [Not eqxa; x; Not a], [], []);
                            (resi2, ResoAST, [x; Not a], [eqp1i1; p1], [])],
                           [resi2]) in
                       (* 4. resolve clauses from 1., 2., and 3. to get `~(x -> y), b, ~a` *)
                       let resi3 = generate_id () in
                       (* 5. generate `a -> b, a` by `impn1`, and `a -> b, ~b` by `impn2` *)
                       let impn1i1 = generate_id () in
                       let impn2i1 = generate_id () in
                       (* 6. resolve clauses from 4. and 5. to get `~(x -> y), a -> b` *)
                       let resi4 = generate_id () in
                       (* 7. generate `x -> y = a -> b, ~(x -> y), ~(a -> b)` by `eqn1` *)
                       let eqn1i = generate_id () in
                       (* 8. resolve 6. and 7. to get `x -> y = a -> b, ~(x -> y)` *)
                       let resi5 = generate_id () in
                       (* 9. generate `~(a -> b), ~a, b` by `impp` *)
                       let imppi2 = generate_id () in
                       (* 10. generate `~(x = a), ~x, a` by `eqp2` and resolve it with premise `x = a` to get `~x, a` *)
                       let notxa, notxai =
                        if x = a then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i2 = generate_id () in
                          let resi6 = generate_id () in
                          ([(eqp1i2, Equp2AST, [Not eqxa; Not x; a], [], []);
                            (resi6, ResoAST, [Not x; a], [eqp1i2; p1], [])],
                           [resi6]) in
                       (* 11. generate `~(y = b), ~b, y` by `eqp1` and resolve it with premise `y = b` to get `y, ~b` *)
                       let ynotb, ynotbi =
                        if y = b then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i2 = generate_id () in
                          let resi7 = generate_id () in
                          ([(eqp1i2, Equp1AST, [Not eqyb; y; Not b], [], []);
                            (resi7, ResoAST, [y; Not b], [eqp1i2; p2], [])],
                           [resi7]) in
                       (* 12. resolve clauses from 9., 10., and 11. to get `~(a -> b), ~x, y` *)
                       let resi8 = generate_id () in
                       (* 13. generate `x -> y, x` by `impn1`, and `x -> y, ~y` by `impn2` *)
                       let impn1i2 = generate_id () in
                       let impn2i2 = generate_id () in
                       (* 14. resolve clauses from 12. and 13. to get `~(a -> b), x -> y` *)
                       let resi9 = generate_id () in
                       (* 15. generate `x -> y = a -> b, x -> y, a -> b` by `eqn2` *)
                       let eqn2i = generate_id () in
                       (* 16. resolve 14. and 15. to get `x -> y = a -> b, x -> y` *)
                       let resi10 = generate_id () in
                       imp @
                       (imppi1, ImppAST, [Not xy; Not x; y], [], []) :: notyb @ xnota @
                       (resi3, ResoAST, [Not xy; b; Not a], [imppi1] @ notybi @ xnotai, []) ::
                       (impn1i1, Impn1AST, [ab; a], [], []) ::
                       (impn2i1, Impn2AST, [ab; Not b], [], []) ::
                       (resi4, ResoAST, [Not xy; ab], [resi3; impn1i1; impn2i1], []) ::
                       (eqn1i, Equn1AST, [eq; Not xy; Not ab], [], []) ::
                       (resi5, ResoAST, [eq; Not xy], [resi4; eqn1i], []) ::
                       (imppi2, ImppAST, [Not ab; Not a; b], [], []) :: notxa @ ynotb @
                       (resi8, ResoAST, [Not ab; Not x; y], [imppi2] @ notxai @ ynotbi, []) ::
                       (impn1i2, Impn1AST, [xy; x], [], []) ::
                       (impn2i2, Impn2AST, [xy; Not y], [], []) ::
                       (resi9, ResoAST, [Not ab; xy], [resi8; impn1i2; impn2i2], []) ::
                       (eqn2i, Equn2AST, [eq; xy; ab], [], []) ::
                       (resi10, ResoAST, [eq; xy], [resi9; eqn2i], []) ::
                       (* 17. resolve 8. and 16. to get `x -> y = a -> b` *)
                       (i, ResoAST, [eq], [resi10; resi5], []) ::
                       process_cong_aux t cog
                     (* xor predicate
                        Convert a proof of the form:
                         -----  -----
                         x = a  y = b
                        --------------cong
                         x + y = a + b

                        to the following derivation:
                        -----  --------------eqp2
                        y = b  ~(y = b), ~y, b
                        ----------------------res  --------------xorp1  ------------xorn1  ---------------------------eqn2
                                ~y, b              ~(x + y), x, y       a + b, a, ~b       x + y = a + b, x + y, a + b
                                --------------------------------------------------------------------------------------res
                                                                     a + b, x, a --(1)
                        -----  --------------eqp1                                                                                                 -----  --------------eqp1
                        y = b  ~(y = b), y, ~b                                                                                                    x = a  ~(x = a), x, ~a
                        ----------------------res  ------------xorn1  --------------xorp1  ---------------------------------eqn1  -----------(1)  ----------------------res 
                                y, ~b              x + y, x, ~y       ~(a + b), a, b       x + y = a + b, ~(x + y), ~(a + b)      a + b, x, a             x, ~a
                                -------------------------------------------------------------------------------------------------------------------------------res
                                                                                              x --(2)
                        -----  ---------------eqp2
                        x = a  ~(x = a), ~x, a
                        ----------------------res  --(2)
                                ~x, a              x
                                --------------------res
                                          a --(3)
                                                                                                     -----  --------------eqp1
                                                                                                     y = b  ~(y = b), y, ~b
                        ---------------------------------eqn1  ------------xorn2  ------------xorn2  ----------------------res  --(3)  --(2)
                        x + y = a + b, ~(x + y), ~(a + b)      a + b, ~a, b       x + y, ~x, y               y, ~b              a      x
                        ----------------------------------------------------------------------------------------------------------------res
                                                                              y --(4)
                        -----  --------------eqp2
                        y = b  ~(y = b), ~y, b
                        ----------------------res  --(4)
                                ~y, b              y
                                --------------------res
                                          b --(5)
                        ----------------xorp2  --(4)  --(2)
                        ~(x + y), ~x, ~y       y      x
                        -------------------------------res
                                   ~(x + y) --(6)
                        ----------------xorp2  --(5)  --(3)
                        ~(a + b), ~a, ~b       b      a
                        -------------------------------res
                                   ~(a + b) --(7)
                        ---------------------------eqn2  --------(6)  --------(7)
                        x + y = a + b, x + y, a + b      ~(x + y)     ~(a + b)
                        ------------------------------------------------------res
                                           x + y = a + b
                     *)
                     | Eq (Xor [x; y], Xor [a; b]) as eq ->
                       let xorxy = Xor [x; y] in
                       let xorab = Xor [a; b] in
                       let eqxa = Eq (x, a) in
                       let eqyb = Eq (y, b) in
                       (* Get premise ids *)
                       let p1 = (match (List.nth ptuples 0) with
                                 | (pid, _) -> pid) in
                       let p2 = (match (List.nth ptuples 1) with
                                 | (pid, _) -> pid) in
                       (* Given x + y = a + b in the conclusion, *)
                       (* 1. Generate ~(y = b), ~y, b by eqp2 and resolve it with y = b to get ~y, b. *)
                       let notyb, notybi =
                        if y = b then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp2i1 = generate_id () in
                          let resi1 = generate_id () in
                          ([(eqp2i1, Equp2AST, [Not eqyb; Not y; b], [], []);
                            (resi1, ResoAST, [Not y; b], [eqp2i1; p2], [])],
                           [resi1]) in
                       (* 2. Resolve 1., ~(x + y), x, y by xorp1, a + b, a, ~b by xorn1, and x + y = a + b, x + y, a + b by eqn2 to get a + b, x, a *)
                       let xorp1i1 = generate_id () in
                       let xorn1i1 = generate_id () in
                       let eqn2i1 = generate_id () in
                       let resi2 = generate_id () in
                       (* 3. Generate ~(y = b), y, ~b by eqp1 and resolve it with y = b to get y, ~b.  *)
                       let ynotb, ynotbi =
                        if y = b then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i1 = generate_id () in
                          let resi3 = generate_id () in
                          ([(eqp1i1, Equp1AST, [Not eqyb; y; Not b], [], []);
                            (resi3, ResoAST, [y; Not b], [eqp1i1; p2], [])],
                           [resi3]) in
                       (* 4. Generate ~(x = a), x, ~a by eqp1 and resolve it with x = a to get x, ~a. *)
                       let xnota, xnotai =
                        if x = a then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i2 = generate_id () in
                          let resi4 = generate_id () in
                          ([(eqp1i2, Equp1AST, [Not eqxa; x; Not a], [], []);
                            (resi4, ResoAST, [x; Not a], [eqp1i2; p1], [])],
                           [resi4]) in
                       (* 5. Resolve 3., x + y, x, ~y by xorn1, ~(a + b), a, b by xorp1, x + y = a + b, ~(x + y), ~(a + b) eqn1, 2., and 4. to get x. *)
                       let xorn1i2 = generate_id () in
                       let xorp1i2 = generate_id () in
                       let eqn1i1 = generate_id () in
                       let resi5 = generate_id () in
                       (* 6. Generate ~(x = a), ~x, a by eqp2 and resolve it with x = a to get ~x, a *)
                       let notxa, notxai =
                        if x = a then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp2i2 = generate_id () in
                          let resi6 = generate_id () in
                          ([(eqp2i2, Equp2AST, [Not eqxa; Not x; a], [], []);
                            (resi6, ResoAST, [Not x; a], [eqp2i2; p1], [])],
                           [resi6]) in
                       (* 7. Resolve 6. and 5. to get a. *)
                       let dera, ai1, ai2 =
                        if x = a then [], [], resi5 (* this derivation is unnecessary and is replaced by a derivation of x (resi5)  *)
                        else
                          let resi7 = generate_id () in
                          ([(resi7, ResoAST, [a], notxai @ [resi5], [])],
                           [resi7],
                           resi7) in
                       (* 8. Resolve x + y = a + b, ~(x + y), ~(a + b) by eqn1 (reuse from 5.), a + b, ~a, b by xorn2, x + y, ~x, y by xorn2, 3., 7., and 5. to get y. *)
                       let xorn2i1 = generate_id () in
                       let xorn2i2 = generate_id () in
                       let resi8 = generate_id () in
                       (* 9. Resolve 1. and 8. to get b. *)
                       let derb, bi =
                        if y = b then [], resi8 (* this derivation is unnecessary and is replaced by a derivation of y (resi8)  *)
                        else
                          let resi9 = generate_id () in
                          ([(resi9, ResoAST, [b], notybi @ [resi8], [])],
                           resi9) in
                       (* 10. Resolve ~(x + y), ~x, ~y by xorp2, 8., and 5. to get ~(x + y). *)
                       let xorp2i1 = generate_id () in
                       let resi10 = generate_id () in
                       (* 11. Resolve ~(a + b), ~a, ~b by xorp2, 9., and 7. to get ~(a + b). *)
                       let xorp2i2 = generate_id () in
                       let resi11 = generate_id () in
                       imp @ notyb @
                       (xorp1i1, Xorp1AST, [Not xorxy; x; y], [], []) ::
                       (xorn1i1, Xorn1AST, [xorab; a; Not b], [], []) ::
                       (eqn2i1, Equn2AST, [eq; xorxy; xorab], [], []) ::
                       (resi2, ResoAST, [xorab; x; a], notybi @ [xorp1i1; xorn1i1; eqn2i1], []) :: ynotb @ xnota @
                       (xorn1i2, Xorn1AST, [xorxy; x; Not y], [], []) ::
                       (xorp1i2, Xorp1AST, [Not xorab; a; b], [], []) ::
                       (eqn1i1, Equn1AST, [eq; Not xorxy; Not xorab], [], []) ::
                       (resi5, ResoAST, [x], ynotbi @ [xorn1i2; xorp1i2; eqn1i1; resi2] @ xnotai, []) :: notxa @ dera @
                       (xorn2i1, Xorn2AST, [xorab; Not a; b], [], []) ::
                       (xorn2i2, Xorn2AST, [xorxy; Not x; y], [], []) ::
                       (resi8, ResoAST, [y], [eqn1i1; xorn2i1; xorn2i2] @ ynotbi @ ai1 @ [resi5], []) :: derb @
                       (xorp2i1, Xorp2AST, [Not xorxy; Not x; Not y], [], []) ::
                       (resi10, ResoAST, [Not xorxy], [xorp2i1; resi8; resi5], []) ::
                       (xorp2i2, Xorp2AST, [Not xorab; Not a; Not b], [], []) ::
                       (resi11, ResoAST, [Not xorab], [xorp2i2; bi; ai2], []) ::
                       (* 12. Resolve x + y = a + b, x + y, a + b by eqn2 (reuse from 2.), 10. and 11. to get x + y = a + b *)
                       (i, ResoAST, [eq], [eqn2i1; resi10; resi11], []) ::
                       process_cong_aux t cog
                     (* ite predicate
                        -----  ---------------eqp2
                        z = c  ~(z = c), ~z, c
                        ----------------------res  ------------------itep1  ----------------iten1  -------------------------------------------eqn2
                                 ~z, c             ~(ite x y z), x, z       ite a b c, a, ~c       ite x y z = ite a b c, ite x y z, ite a b c
                                --------------------------------------------------------------------------------------------------------------res
                                                                   ite x y z = ite a b c, ite a b c, x, a --(1)
                        -----  ---------------eqp1                                                                                                                                                   -----  ---------------eqp1
                        z = c  ~(z = c), z, ~c                                                                                                                                                       x = a  ~(x = a), x, ~a
                        ----------------------res  ----------------iten1  ------------------itep1  -------------------------------------------------eqn1  --------------------------------------(1)  ----------------------res
                                 z, ~c             ite x y z, x, ~z       ~(ite a b c), a, c       ite x y z = ite a b c, ~(ite x y z), ~(ite a b c)      ite x y z = ite a b c, ite a b c, x, a              x, ~a
                                 ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------res  
                                                                                                           ite x y z = ite a b c, x --(2)
                        -----  ---------------eqp2
                        x = a  ~(x = a), ~x, a
                        ----------------------res  ------------------------(2)
                                 ~x, a             ite x y z = ite a b c, x
                                 ------------------------------------------res
                                        ite x y z = ite a b c, a --(3)
                        y = b  ~(y = b), y, ~b
                        ----------------------res  -------------------itep2  -----------------iten2  -------------------------------------------eqn2  ------------------------(3)  ------------------------(2)
                                 y, ~b             ~(ite a b c), ~a, b       ite x y z, ~x, ~y       ite x y z = ite a b c, ite x y z, ite a b c      ite x y z = ite a b c, a     ite x y z = ite a b c, x
                                 --------------------------------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                                     ite x y z = ite a b c, ite x y z --(4)
                     
                        -------------------------------------------------eqn1  --------------------------------(4)
                        ite x y z = ite a b c, ~(ite x y z), ~(ite a b c)      ite x y z = ite a b c, ite x y z
                        ---------------------------------------------------------------------------------------res
                                                ite x y z = ite a b c, ~(ite a b c) --(5)
                        -------------------itep2  --------------------------------(4)  ------------------------(2)
                        ~(ite x y z), ~x, y       ite x y z = ite a b c, ite x y z     ite x y z = ite a b c, x
                        ---------------------------------------------------------------------------------------res
                                                      ite x y z = ite a b c, y --(6)
                        -----------------iten2  -----------------------------------(5)  -----------------------(3)
                        ite a b c, ~a, ~b       ite x y z = ite a b c, ~(ite a b c)     ite x y z = ite a b c, a
                        ----------------------------------------------------------------------------------------res
                                                      ite x y z = ite a b c, ~b --(7)
                        -----  ---------------eqp2
                        y = b  ~(y = b), ~y, b
                        ----------------------res  ------------------------(6)  -------------------------(7)
                                 ~y, b             ite x y z = ite a b c, y     ite x y z = ite a b c, ~b
                                 ------------------------------------------------------------------------res
                                                           ite x y z = ite a b c  
                     *)
                     | Eq (Ite [x; y; z], Ite [a; b; c]) as eq ->
                       (* Get premise ids *)
                       let p1 = (match (List.nth ptuples 0) with
                                 | (pid, _) -> pid) in
                       let p2 = (match (List.nth ptuples 1) with
                                 | (pid, _) -> pid) in
                       let p3 = (match (List.nth ptuples 2) with
                                 | (pid, _) -> pid) in
                       let itexyz = Ite [x; y; z] in
                       let iteabc = Ite [a; b; c] in
                       (* Given ite x y z = ite a b c in the conclusion,
                          1. Generate ~(z = c), ~z, c by eqp2 and resolve it with z = c to get ~z, c *)
                       let notzc, notzci = 
                        if z = c then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp2i1 = generate_id () in
                          let resi1 = generate_id () in
                          ([(eqp2i1, Equp2AST, [Not (Eq (z, c)); Not z; c], [], []);
                            (resi1, ResoAST, [Not z; c], [eqp2i1; p3], [])],
                           [resi1]) in
                       (* 2. Resolve 1., ~(ite x y z), x, z by itep1, ite a b c, a, ~c by iten1, and ite x y z = ite a b c, ite x y z, ite a b c by 
                             eqn2 to get ite x y z = ite a b c, ite a b c, x, a *)
                       let itep1i1 = generate_id () in
                       let iten1i1 = generate_id () in
                       let eqn2i1 = generate_id () in
                       let resi2 = generate_id () in
                       (* 3. Generate ~(z = c), z, ~c by eqp1 and resolve it with z = c to get z, ~c *)
                       let znotc, znotci =
                        if z = c then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i1 = generate_id () in
                          let resi3 = generate_id () in
                          ([(eqp1i1, Equp1AST, [Not (Eq (z, c)); z; Not c], [], []);
                            (resi3, ResoAST, [z; Not c], [eqp1i1; p3], [])],
                           [resi3]) in
                       (* 4. Generate ~(x = a), x, ~a by eqp1 and resolve it with x = a to get x, ~a *)
                       let xnota, xnotai = 
                        if x = a then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i2 = generate_id () in
                          let resi4 = generate_id () in
                          ([(eqp1i2, Equp1AST, [Not (Eq (x, a)); x; Not a], [], []);
                            (resi4, ResoAST, [x; Not a], [eqp1i2; p1], [])],
                           [resi4]) in
                       (* 5. Resolve 3., ite x y z, x, ~z by iten1, ~(ite a b c), a, c by itep1, ite x y z = ite a b c, ~(ite x y z), ~(ite a b c) by
                             eqn1, 2., and 4. to get ite x y z = ite a b c, x *)
                       let iten1i2 = generate_id () in
                       let itep1i2 = generate_id () in
                       let eqn1i1 = generate_id () in
                       let resi5 = generate_id () in
                       (* 6. Generate ~(x = a), ~x, a by eqp2 and resolve it with x = a to get ~x, a *)
                       let notxa, notxai =
                        if x = a then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp2i2 = generate_id () in
                          let resi6 = generate_id () in
                          ([(eqp2i2, Equp2AST, [Not (Eq (x, a)); Not x; a], [], []);
                            (resi6, ResoAST, [Not x; a], [eqp2i2; p1], [])],
                           [resi6]) in
                       (* 7. Resolve 6. and 5. to get ite x y z = ite a b c, a *)
                       let eqa, eqai1, eqai2 =
                        if x = a then [], [], resi5 (* this derivation is unnecessary and unsound for refl equality, except in one place where it is replaced by derivation resi5 *)
                        else
                          let resi7 = generate_id () in
                          ([(resi7, ResoAST, [eq; a], notxai @ [resi5], [])],
                           [resi7],
                           resi7) in
                       (* 8. Generate ~(y = b), y, ~b by eqp1 amd resolve it with y = b to get y, ~b. *)
                       let ynotb, ynotbi =
                        if y = b then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp1i3 = generate_id () in
                          let resi8 = generate_id () in
                          ([(eqp1i3, Equp1AST, [Not (Eq (y, b)); y; Not b], [], []);
                            (resi8, ResoAST, [y; Not b], [eqp1i3; p2], [])],
                           [resi8]) in
                       (* 9. Resolve 8., ~(ite a b c), ~a, b by itep2, ite x y z, ~x, ~y by iten2, ite x y z = ite a b c, ite x y z, ite a b c by eqn2 (reuse from 2.), 
                             7., and 5. to get ite x y z = ite a b c, ite x y z *)
                       let itep2i1 = generate_id () in
                       let iten2i1 = generate_id () in
                       let resi9 = generate_id () in
                       (* 10. Generate ite x y z = ite a b c, ~(ite x y z), ~(ite a b c) by eqn1 (reuse from 5.) and resolve it with 9. to get 
                              ite x y z = ite a b c, ~(ite a b c) *)
                       let resi10 = generate_id () in
                       (* 11. Generate ~(ite x y z), ~x, y by itep2, 9. and 5. to get ite x y z = ite a b c, y *)
                       let itep2i2 = generate_id () in
                       let resi11 = generate_id () in
                       (* 12. Generate ite a b c, ~a, ~b by iten2 and resolve it with 10. and 7. to get ite x y z = ite a b c, ~b *)
                       let iten2i2 = generate_id () in
                       let resi12 = generate_id () in
                       (* 13. Generate ~(y = b), ~y, b by eqp2 and resolve it with y = b to get ~y, b *)
                       let notyb, notybi =
                        if y = b then [], [] (* this derivation is unnecessary and unsound for refl equality *)
                        else
                          let eqp2i3 = generate_id () in
                          let resi13 = generate_id () in
                          ([(eqp2i3, Equp2AST, [Not (Eq (y, b)); Not y; b], [], []);
                            (resi13, ResoAST, [Not y; b], [eqp2i3; p2], [])],
                           [resi13]) in
                       imp @ notzc @
                       (itep1i1, Itep1AST, [Not itexyz; x; z], [], []) ::
                       (iten1i1, Iten1AST, [iteabc; a; Not c], [], []) ::
                       (eqn2i1, Equn2AST, [eq; itexyz; iteabc], [], []) ::
                       (resi2, ResoAST, [eq; iteabc; x; a], notzci @ [itep1i1; iten1i1; eqn2i1], []) :: znotc @ xnota @
                       (iten1i2, Iten1AST, [itexyz; x; Not z], [], []) ::
                       (itep1i2, Itep1AST, [Not iteabc; a; c], [], []) ::
                       (eqn1i1, Equn1AST, [eq; Not itexyz; Not iteabc], [], []) ::
                       (resi5, ResoAST, [eq; x], znotci @ [iten1i2; itep1i2; eqn1i1; resi2] @ xnotai, []) :: notxa @ eqa @ ynotb @ 
                       (itep2i1, Itep2AST, [Not iteabc; Not a; b], [], []) ::
                       (iten2i1, Iten2AST, [itexyz; Not x; Not y], [], []) ::
                       (resi9, ResoAST, [eq; itexyz], ynotbi @ [itep2i1; iten2i1; eqn2i1] @ eqai1 @ [resi5], []) ::
                       (resi10, ResoAST, [eq; Not iteabc], [eqn1i1; resi9], []) ::
                       (itep2i2, Itep2AST, [Not itexyz; Not x; y], [], []) ::
                       (resi11, ResoAST, [eq; y], [itep2i2; resi9; resi5], []) ::
                       (iten2i2, Iten2AST, [iteabc; Not a; Not b], [], []) ::
                       (resi12, ResoAST, [eq; Not b], [iten2i2; resi10; eqai2], []) :: notyb @
                       (* 14. Resolve 13., 11., and 12. to get ite x y z = ite a b c *)
                       (i, ResoAST, [eq], notybi @ [resi11; resi12], []) ::
                       process_cong_aux t cog
                     (* not predicate
                         -----
                         x = a
                        --------cong
                         ~x = ~a

                        Encoding
                        ========
                        -----  ---------------eqp2                       -----   ---------------eqp1
                        x = a  ~(x = a), ~a, x                           x = a   ~(x = a), ~x, a      
                        -----------------------res  ---------------eqn2  ------------------------res    --------------eqn1
                               ~a, x                ~x = ~a, ~x, ~a              ~x, a                 ~x = ~a, x, a     
                               ------------------------------------res          -------------------------------------res
                                            ~a, ~x = ~a                                       a, ~x = ~a
                                            ------------------------------------------------------------res
                                                                        ~x = ~a                  
                     *)
                     | Eq (Not x, Not a) ->
                        (* Given `~x = ~a` in the conclusion, *)
                        (* 1. generate `~(x = a), ~x, a` by `eqp1` and resolve it with `x = a`, to get `~x, a` *)
                        let eqp1i = generate_id () in
                        let resi1 = generate_id () in
                        let pxa = (match (try (List.hd ptuples) with | Failure _ -> raise (Debug 
                                          ("| process_cong: no premises found in cong over negation case at id "^i^" |"))) with
                                 | (pid, _) -> pid) in
                        (* 2. generate `~x = ~a, x, a` by `eqn1` *)
                        let eqn1i = generate_id () in
                        (* 3. resolve 1. and 2. to get `a, ~x = ~a` *)
                        let resi2 = generate_id () in
                        (* 4. generate `~(x = a), ~a, x` by `eqp2` and resolve it with `x = a`, to get `~a`, x` *)
                        let eqp2i = generate_id () in
                        let resi3 = generate_id () in
                        (* 5. generate `~x = ~a, ~x, ~a` by `eqn2` *)
                        let eqn2i = generate_id () in
                        (* 6. resolve 4. and 5. to get `~a, ~x = ~a` *)
                        let resi4 = generate_id () in
                        let eqxa = Eq (x, a) in
                        imp @
                        (eqp1i, Equp1AST, [Not eqxa; Not x; a], [], []) ::
                        (resi1, ResoAST, [Not x; a], [eqp1i; pxa], []) ::
                        (eqn1i, Equn1AST, [eq; x; a], [], []) ::
                        (resi2, ResoAST, [eq; a], [resi1; eqn1i], []) ::
                        (eqp2i, Equp2AST, [Not eqxa; Not a; x], [], []) ::
                        (resi3, ResoAST, [Not a; x], [eqp2i; pxa], []) :: 
                        (eqn2i, Equn2AST, [eq; Not x; Not a], [], []) :: 
                        (resi4, ResoAST, [eq; Not a], [resi3; eqn2i], []) ::
                        (* 7. resolve 3. and 6. to get `~x = ~a` *)
                        (i, ResoAST, [eq], [resi2; resi4], []) ::
                        process_cong_aux t cog
                     (* User-defined predicates, predicates over non-bool connectives (ex: <), etc. *)
                     | _ ->
                        (*
                           Convert a proof of the form:
                           ...
                           x = a              y = b
                           ------------------------cong
                               P(x, y) = P(a, b)

                           to:
                              (1)                                    (2)                  (3)                                     (4)
                           ------------------------------------------------res        -------------------------------------------------res
                           ~(x = a), ~(y = b), P(a, b), (P(x, y) = P(a, b))           ~(x = a), ~(y = b), ~P(a, b), (P(x, y) = P(a, b))      x = a    y = b
                           ---------------------------------------------------------------------------------------------------------------------------------res
                                                                                    P(x, y) = P(a, b)
                           where:
                           -------------------------------------eqcongp
                           ~(x = a), ~(y = b), ~P(x, y), P(a, b)     --(1)
                           -------------------------------------eqn2
                           (P(x, y) = P(a, b)), P(x, y), P(a, b)      --(2)
                           -------------------------------------eqcongp
                           ~(x = a), ~(y = b), ~P(a, b), P(x, y)     --(3)
                           ---------------------------------------eqn1
                           (P(x, y) = P(a, b)), ~P(x, y), ~P(a, b)    --(4) 
                        *)
                        let eqcpi1 = generate_id () in
                        let eqcpi2 = generate_id () in
                        let eqn2i = generate_id () in
                        let eqn1i = generate_id () in
                        let resi1 = generate_id () in
                        let resi2 = generate_id () in
                        (* variables for the target equality and the predicates it equates *)
                        let (p1, p2) = (match conc with
                                        | Eq (x, y) -> (x, y)
                                        | _ -> assert false) in
                          imp @
                          ((eqcpi1, EqcpAST, (prem_negs @ [Not p1; p2]), [], []) ::
                           (eqn2i, Equn2AST, [conc; p1; p2], [], []) ::
                           (resi1, ResoAST, (prem_negs @ [conc; p2]), [eqcpi1; eqn2i], []) ::
                           (eqcpi2, EqcpAST, (prem_negs @ [Not p2; p1]), [], []) ::
                           (eqn1i, Equn1AST, [conc; Not p1; Not p2], [], []) ::
                           (resi2, ResoAST, (prem_negs @ [conc; Not p2]), [eqcpi2; eqn1i], []) ::
                           (i, ResoAST, [conc], resi1 :: resi2 :: pids, []) ::
                           process_cong_aux t cog))
                else
                  raise (Debug ("| process_cong: expecting head of clause to be either an equality or an iff at id "^i^" |")))
          | _ -> raise (Debug ("| process_cong: expecting clause to have one literal at id "^i^" |")))
    | (i, r, cl, p, a) :: t -> (* This is necessary to add the shared terms to the hash tables *)
                               let _ = try process_cl cl with
                                       | Form.NotWellTyped frm -> raise (Debug ("| process_cong: formula "^
                                          (Form.pform_to_string frm)^" is not well-typed at id "^i^" |")) in
                               (i, r, cl, p, a) :: process_cong_aux t cog
    | [] -> []
    in process_cong_aux c c


(* Removing occurrences of the trans rule using other rules 
   including eq_transitive, reso *)
(*let rec last (l : 'a list) : 'a =
  match l with
  | [] -> raise (Debug ("| last: trying to find the last element of an empty list |"))
  | [x] -> x
  | h :: t -> last t
let rec allbutlast (l : 'a list) : 'a =
  match List.rev l with
  | [] -> []
  | h :: tl -> List.rev tl*)
let process_trans (c : certif) : certif =
  let rec process_trans_aux (c : certif) (cog : certif) : certif =
    match c with
     | (i, TransAST, cl, p, a) :: t -> 
        (* To differentiate between the formula and term case, we need to process
           the clause because we treat equality and iff as the same at the AST level *)
        let c' = try process_cl cl with
           | Form.NotWellTyped frm -> raise (Debug ("| process_trans: formula "^
              (Form.pform_to_string frm)^" is not well-typed at id "^i^" |")) in
        (match c' with
          | l :: _ ->
             (* get negation of premises and terms for any implicit equality *)
             let prem_negs = List.map (fun x -> (match (get_cl x cog) with
                                                 | Some x' -> (try Not (List.find (fun y -> match (get_expr y) with
                                                                             | Eq _ -> true
                                                                             | _ -> false) x') with
                                                             | Not_found -> raise (Debug ("| process_trans: premise "^x^" to cong has no equalities |")))
                                                 | None -> raise (Debug ("| process_trans: can't fetch premises to trans at id "^i^" |")))) p in
             (* transitivity over terms *)
             if is_eq l then
               (*
                  Convert a proof of the form:
                  ...
                  a = b    b = c    c = d
                  -----------------------trans
                           a = d
                           
                  to:
                  ...
                  -----------------------------------eqtrans
                  ~(a = b), ~(b = c), ~(c = d), a = d         a = b    b = c    c = d
                  -------------------------------------------------------------------res
                                                  a = d
               *)
               let eqti = generate_id () in
               [(eqti, EqtrAST, prem_negs @ cl, [], []);
                (i, ResoAST, cl, eqti :: p, [])] @
               (process_trans_aux t cog)
             (* transitivity over formulas *)
             else if is_iff l then
               (* trans over single premise can occur if all other premises have been eliminated, 
                  e.g., by notnot elimination *)
               if List.length p = 1 then
                 let phd = (try (List.hd p) with | Failure _ -> raise (Debug 
                              ("| process_trans : no premise to trans found at id "^i^" |"))) in
                 let prem = (match (get_cl phd cog) with
                             | Some x -> x
                             | None -> raise (Debug ("| process_trans: can't fetch premise to trans at id "^i^" |"))) in
                 (i, ResoAST, prem, p, []) :: process_trans_aux t cog
               else
                 (*
                    Convert a proof of the form:
                    -----  -----
                    a = b  b = c
                    ------------trans
                        a = c
  
                    to one of the form:
                    (1)   (2)
                    ---------res
                      a = c
                    where (1) and (2) are derived as:
                    ---------------eqp1  -----     ---------------eqp1  -----
                    ~(a = b), a, ~b      a = b     ~(b = c), b, ~c      b = c
                    --------------------------res  --------------------------res 
                               a, ~b                          b, ~c
                               ------------------------------------res    -----------eqn2
                                               a, ~c                      a = c, a, c
                                               --------------------------------------res
                                                              a = c, a   ---(1)
  
                    ---------------eqp2  -----      ---------------eqp2  -----
                    ~(b = c), ~b, c      b = c      ~(a = b), ~a, b      a = b
                    --------------------------res  --------------------------res
                               ~b, c                          ~a, b
                               ------------------------------------res    -------------eqn1
                                               ~a, c                      a = c, ~a, ~c
                                               ----------------------------------------res
                                                              a = c, ~a   ---(2)   
                 *)
                 let p' = List.map (fun x -> match get_cl x cog with
                         | Some x' -> let x'hd = (try (List.hd x') with | Failure _ -> raise 
                                                   (Debug ("| process_trans: premise "^x^" returns an empty clause in id "^i^" |"))) in
                                      let x', y' = (match (get_expr x'hd) with
                                                   | Eq (x'', y'') -> (x'', y'')
                                                   | _ -> raise (Debug ("| process_trans: expecting premise of trans to be iff at id "^i^" |"))) in
                                      (x, (x', y'))
                         | None -> raise (Debug ("| process_trans: can't fetch premises to `and` at id "^i^" |"))) p in
                 let eq = (try (List.hd cl) with | Failure _ -> 
                           raise (Debug ("| process_trans: clause produced by trans is empty at id "^i^" |"))) in
                 let x1, xn = (match (get_expr eq) with
                              | Eq (x', y') -> x', y'
                              | _ -> raise (Debug ("| process_trans: expecting premise of trans to be iff at id "^i^" |"))) in
                 (* Reorder premise equalities from p' to account for any implicit symmetries, a boolean value is set to tue if the equality has been reordered *)
                 let _, p' = List.fold_left 
                  (fun (t, l) (pid, (px, py)) ->
                    if t = px then 
                      (py,
                       (pid, (px, py), false) :: l)
                    else if t = py then
                      (px,
                       (pid, (py, px), true) :: l)
                    else 
                      raise (Debug ("| process_trans: failing to find transitive equality in premises at id "^i^" |"))) 
                  (x1, []) p' in
                 (* Given conclusion `x1 = xn` and premises `x1 = x2, ..., xn-1 = xn`, *)
                 (* 1. For each premise `x = y`, generate `~(x = y), x, ~y` by `eqp1` and resolve it with 
                       `x = y` to get `x, ~y` *)
                 let eqp1is, eqp1s = List.fold_left
                   (fun (is, r) (pid, (px, py), reord) ->
                     let i' = generate_id () in
                     let eqpi = generate_id () in
                     let eqstep = 
                      if reord then (eqpi, Equp2AST, [Not (Eq (py, px)); py; Not px], [], []) 
                      else (eqpi, Equp1AST, [Not (Eq (px, py)); px; Not py], [], []) in
                     (i' :: is,
                      eqstep :: (i', ResoAST, [px; Not py], [eqpi; pid], []) :: r))
                   ([], []) p' in
                 (* 2. Resolve all clauses from 1. to get `x1, ~xn` *)
                 let resi1 = generate_id () in
                 (* 3. Generate `x1 = xn, x1, xn` by `eqn2` *)
                 let eqn2i = generate_id () in
                 (* 4. Resolve 2. and 3. to get `x1 = xn, x1`. *)
                 let resi2 = generate_id () in
                 (* 5. For each premise `x = y`, generate `~(x = y), ~x, y` by `eqp2` and resolve it with 
                       `x = y` to get `~x, y` *)
                 let eqp2is, eqp2s = List.fold_left
                   (fun (is, r) (pid, (px, py), reord) ->
                     let i' = generate_id () in
                     let eqpi = generate_id () in
                     let eqstep =
                      if reord then (eqpi, Equp1AST, [Not (Eq (py, px)); Not py; px], [], [])
                      else (eqpi, Equp2AST, [Not (Eq (px, py)); Not px; py], [], []) in
                     (i' :: is,
                      eqstep :: (i', ResoAST, [Not px; py], [eqpi; pid], []) :: r))
                   ([], []) p' in
                 (* 6. Resolve all clauses from 5. to get `~x1, xn` *)
                 let resi3 = generate_id () in
                 (* 7. Generate `x1 = xn, ~x1, ~xn` by `eqn1` *)
                 let eqn1i = generate_id () in
                 (* 8. Resolve 6. and 7. to get `x1 = xn, ~x1`. *)
                 let resi4 = generate_id () in
                 (* 9. resolve 4. and 8. to get `x1 = xn` *)
                 eqp1s @
                 ((resi1, ResoAST, [x1; Not xn], eqp1is, []) ::
                  (eqn2i, Equn2AST, [eq; x1; xn], [], []) ::
                  (resi2, ResoAST, [eq; x1], [resi1; eqn2i], []) :: eqp2s) @
                 ((resi3, ResoAST, [Not x1; xn], eqp2is, []) :: 
                  (eqn1i, Equn1AST, [eq; Not x1; Not xn], [], []) ::
                  (resi4, ResoAST, [eq; Not x1], [resi3; eqn1i], []) ::
                  (i, ResoAST, [eq], [resi2; resi4], []) ::
                  process_trans_aux t cog)
             else
               raise (Debug ("| process_trans: expecting head of clause to be either an equality or an iff at id "^i^" |"))
          | _ -> raise (Debug ("| process_trans: expecting clause to have one literal at id "^i^" |")))
     | (i, ReflAST, cl, p, a) :: t -> 
        (* To differentiate between the formula and term case, we need to process
           the clause because we treat equality and iff as the same at the AST level *)
        let c' = try process_cl cl with
           | Form.NotWellTyped frm -> raise (Debug ("| process_trans: in refl rule, formula "^
              (Form.pform_to_string frm)^" is not well-typed at id "^i^" |")) in
        (match c' with
          (* We need to encode the formula case, the checker can handle the term case *)
          | l :: _ when is_iff l ->
             (* Convert:
                --------refl
                 x = x
                to:
                ---------eqn1  ---------eqn2
                x = x, ~x       x = x, x
                ------------------------res
                           x = x
             *)
             (match cl with
             | [Eq (x, y) as eq] when x = y ->
                let eqn1i = generate_id () in
                let eqn2i = generate_id () in
                (eqn1i, Equn1AST, [eq; Not x], [], []) ::
                (eqn2i, Equn2AST, [eq; x], [], []) ::
                (i, ResoAST, [eq], [eqn1i; eqn2i], []) 
                :: process_trans_aux t cog
             | _ -> raise (Debug ("| process_trans: expecting clause for refl to be a singleton iff at id "^i^" |")))
          | _ -> (i, ReflAST, cl, p, a) :: process_trans_aux t cog)
     | h :: t -> h :: (process_trans_aux t cog)
     | [] -> []
   in process_trans_aux c c


(* SMTCoq requires projection rules and, not_or, or_neg, and_pos
   to specify an integer argument specifying the term to project.
   Alethe doesn't specify the projection for these rules. This 
   transformation searches the clause for the projection and adds
   it as an argument *)
let rec process_proj (c: certif): certif =
  let rec aux (c: certif) (cog: certif) : certif =
    match c with
    | (i, AndAST, cl, p, a) :: tl when a = [] ->
        let p' = List.map (fun x -> (match get_cl x cog with
                           | Some x' -> let x'hd = (try (List.hd x') with | Failure _ -> raise 
                                         (Debug ("| process_proj: premise "^x^" is an empty clause at id "^i^" |"))) in
                                        x'hd
                           | None -> raise (Debug ("| process_proj: can't fetch premises to `and` at id "^i^" |"))))
                 p in
        (match (get_expr (try (List.hd p') with | Failure _ -> 
                          raise (Debug ("| process_proj: and rule has no premises at id "^i^" |")))), 
               (get_expr (try (List.hd cl) with | Failure _ -> 
                raise (Debug ("| process_proj: clause produced by and is empty at id "^i^" |"))))
         with
        | And ts, x ->
            let i' = try findi (term_eq x) ts with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "
                        ^i^" |"^s)) in
              (i, AndAST, cl, p, [(string_of_int i')]) :: aux tl cog
        | _, _ -> raise (Debug ("| process_proj: expecting premise to be an `and` at id "
                         ^i^" |")))
    | (i, NorAST, cl, p, a) :: tl when a = [] ->
        let p' = List.map (fun x -> match get_cl x cog with
                           | Some x' -> let x'hd = (try (List.hd x') with | Failure _ -> raise 
                                         (Debug ("| process_proj: premise "^x^" is an empty clause at id "^i^" |"))) in
                                        x'hd
                           | None -> raise (Debug ("| process_proj: can't fetch premises to `and` at id "^i^" |")))
                 p in
        (match (get_expr (try (List.hd p') with | Failure _ -> 
                         raise (Debug ("| process_proj: not_or rule has no premises at id "^i^" |")))), 
               (get_expr (try (List.hd cl) with | Failure _ -> 
                         raise (Debug ("| process_proj: clause produced by not_or is empty at id "^i^" |")))) with
        | Not (Or ts), Not x -> 
            let i' = try findi (term_eq x) ts with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "^i^" |"^s)) in
              (i, NorAST, cl, p, [(string_of_int i')]) :: aux tl cog
        | _, _ -> raise (Debug ("| process_proj: expecting premise to be a `not or` at id "
                  ^i^" |")))
    | (i, OrnAST, cl, p, a) :: tl when a = [] ->
        (match get_expr (List.nth cl 0), get_expr (List.nth cl 1) with
        | Or ts, Not x -> 
            let i' = try findi (term_eq x) ts with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "^i^" |"^s)) in
              (i, OrnAST, cl, p, [(string_of_int i')]) :: aux tl cog
        | _, _ -> raise (Debug 
                  ("| process_proj: expecting clause with `or` and `not` at id "^i^" |")))
    | (i, AndpAST, cl, p, a) :: tl when a = [] ->
        (match get_expr (List.nth cl 0), get_expr (List.nth cl 1) with
        | Not (And ts), x ->
            let i' = try findi (term_eq x) ts with
                     | Debug s -> raise (Debug ("| process_proj: fails at id "^i^" |"^s)) in
              (i, AndpAST, cl, p, [(string_of_int i')]) :: aux tl cog
        |  _, _ -> raise (Debug ("| process_proj: expecting clause with `not and` and projection at id "
                   ^i^" |")))
    | (i, SubproofAST subcl, cl, p, a) :: tl -> (i, SubproofAST (process_proj subcl), cl, p, a) :: aux tl cog
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
| [H]  |                                [(H ^ ~G), ~H, G]
| Pi_2 |                                ...
|  G   |                                Pi_3'
--------               ----->           ...      ------------and_pos
 [~H, G] --(1)                          H ^ ~G   ~(H ^ ~G), H
...                                     ---------------------res            -------------and_pos
  Pi_3                                            H                H ^ ~G   ~(H ^ ~G), ~G
...                                              Pi_2             ----------------------res
   []                                             G                          ~G
                                                  -----------------------------res
                                                                []
where        
 - Pi_3' replaces every step in Pi_3 that directly or indirectly uses (1), so that the result 
   naturally produces the original result v (H ^ ~G) 
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
  let pi3hd = (try (List.hd p) with | Failure _ -> raise (Debug ("| extend_cl_aux: no premises to rule |"))) in
  match r, (get_cl pi3hd pi3) with
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
  | AndAST, Some [And xs] -> 
      let ahd = try (List.hd a) with | Failure _ -> raise (Debug ("| extend_cl_aux: no args to `and` rule |")) in
      let n = int_of_string ahd in
      (AndpAST, [Not (And xs); List.nth xs n])
  | NorAST, Some [Not (Or xs)] -> 
      let ahd = try (List.hd a) with | Failure _ -> raise (Debug ("| extend_cl_aux: no args to `not_or` rule |")) in
      let n = int_of_string ahd in
      (OrnAST, [Or xs; List.nth xs n])
  | Nimp1AST, Some [Not (Imp xs)] -> (Impn1AST, [Imp xs; List.nth xs 0])
  | Nimp2AST, Some [Not (Imp xs)] -> (Impn2AST, [Imp xs; Not (List.nth xs 1)])
  | r, Some t -> raise (Debug ("| extend_cl_aux: unexpected rule "^(string_of_rule r)^
                        "to extend_cl, or premise "^(string_of_clause t)^" to the rule at id "^pi3hd^" |"))
  | r, None -> raise (Debug ("| extend_cl_aux: rule "^(string_of_rule r)^" has no premise"^" |")) 
let rec extend_cl (andn_id : id) (h : term) (g : term) (pi3 : certif) (pi3og : certif): certif =
  match pi3 with
  | (i, r, cl, p, a) :: tl when
      (* Resolution/weaken that directly uses andn_id *)
      (r = ResoAST || r = ThresoAST || r = WeakenAST)
              &&
      ((List.mem andn_id p)
              ||
      (* Resolution that indirectly uses andn_id *)
      (List.exists (fun x -> List.mem x (get_cids andn_id)) p)) ->
        add_cid andn_id i;
        (i, r, ((And [h; Not g])) :: cl, p, a) :: extend_cl andn_id h g tl pi3og
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
        let rul, claus = try extend_cl_aux r p a pi3og with
                         | Debug s -> raise (Debug ("| extend_cl : failed at id "^i^" |"^s)) in
        let taut_id = generate_id () in
        (taut_id, rul, claus, [], a) ::                    (* (1) *)
        (i, ResoAST, ((And [h; Not g]) :: List.tl claus), taut_id :: p, []) ::  (* (2) *)
        extend_cl andn_id h g tl pi3og
  | hd :: tl -> hd :: (extend_cl andn_id h g tl pi3og)
  | [] -> []
let process_subproof_aux (andn_id : id) (new_h_id : id) (g_id : id) (pi2 : certif ) (pi3 : certif) (h : term) (g : term) : certif =
  let revpi3hd = try (List.hd (List.rev pi3)) with | Failure _ -> raise (Debug 
               ("| process_subproof_aux: subproof step is the last step of the proof, this is unexpected |")) in
  let (andi, andc) = match revpi3hd with
                     | (i, _, c, _, _) -> (i, c) in
  let andpi1 = generate_id () in
  let andpi2 = generate_id () in
  let notg_id = generate_id () in
  (* Replace the discharge step proving (~h v g) by a tautological proof of (h ^ ~g) v ~h v g *)
  let t' = [And [h; Not g]; Not h; g] in
  let pi3' = extend_cl andn_id h g pi3 ((andn_id, AndnAST, t', [], []) :: pi3) in
  ((andn_id, AndnAST, t', [], []) ::
    pi3') @
  ((andpi1, AndpAST, [Not (And [h; Not g]); h], [], ["0"]) ::
   (new_h_id, ResoAST, h :: andc, [andi; andpi1], []) :: pi2) @
  [(andpi2, AndpAST, [Not (And [h; Not g]); Not g], [], ["1"]);
   (notg_id, ResoAST, Not g :: andc, [andi; andpi2], []);
   (generate_id (), ResoAST, andc, [g_id; notg_id], [])]

let rec process_subproof (c : certif) : certif =
  match c with
  | (i, SubproofAST cert, cl, p, a) :: pi3' ->
      if List.length cert < 2 then
         raise (Debug ("| process_subproof: expecting length of subproof to be at least 2 steps at id "^i^" |"))
      else
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
             (try process_subproof_aux andn_id new_h_id g_id pi2 pi3 h g with
             | Debug s -> raise (Debug ("| process_subproof: failed at id "^i^" |"^s)))
         | _ -> raise (Debug ("| process_subproof: expecting the last step of the certificate to be a discharge step at id "^i^" |")))
  | h :: tl -> h :: process_subproof tl
  | [] -> clear_cids (); []


(* Process _simplify rules from Alethe 
   Each rule has multiple variants, all taking the form
   a <-> b
   To prove a <-> b:
   1. Prove ~a v b via subproof discharge
   2. Prove ~b v a via subproof discharge
   3. Prove a <-> b v ~a v ~b via equiv_neg1
   4. Prove a <-> b by resolving 3,2,1
   ---------------eqn1    -----subp      -------------eqn2  ------subp
   a <-> b, ~a, ~b        ~a, b          a <-> b, a, b      a, ~b
   --------------------------------res   ------------------------res
              a <-> b, ~a                      a <-> b, a
              -------------------------------------------res
                                 a <-> b
*)
(* This is a cool function but currently useless since the two places 
   we can use them (process_notnot and process_simpify_ltr) have many case
   specific requirements, but in the future, we may be able to generalize 
   this if we find that it will save some repeated work.
   
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
(* TODO: _simplify rules need to be applied to a fixpoint, we are currently not doing that. I don't imagine 
   this would be a complicated extension, but need to think about it more *) 
let simplify_to_subproof (i: id) (a2bi: id) (b2ai: id) (a: term) (b: term) (a2b: certif) (b2a: certif) : certif =
  let sp1id = generate_id () in
  let subp1 = (a2bi, AssumeAST, [a], [], []) ::
              (a2b @ 
              [(sp1id, DischargeAST, [Not a; b], [], [])]) in
  let sp2id = generate_id () in
  let subp2 = (b2ai, AssumeAST, [b], [], []) ::
              (b2a @ 
              [(sp2id, DischargeAST, [Not b; a], [], [])]) in
  let eq1i = generate_id () in
  let eq2i = generate_id () in
  let resi1 = generate_id () in
  let resi2 = generate_id () in
  [(eq1i, Equn1AST, [Eq (a, b); Not a; Not b], [], []);
   (generate_id (), SubproofAST subp1, [], [], []);
   (resi1, ResoAST, [Eq (a, b); Not a], [sp1id; eq1i], []);
   (eq2i, Equn2AST, [Eq (a, b); a; b], [], []);
   (generate_id (), SubproofAST subp2, [], [], []);
   (resi2, ResoAST, [Eq (a, b); a], [sp2id; eq2i], []);
   (i, ResoAST, [Eq (a, b)], [resi1; resi2], [])]

(* are t1 and t2 negations of each other? *)
let is_neg (t1 : term) (t2 : term) : bool =
  match t1, t2 with
  | t, Not t' when t' = t -> true
  | Not t, t' when t' = t -> true
  | _ -> false
(* repeat x n returns list with n x's
let repeat (x : 'a) (n : int) : 'a list =
  let rec repeat' (x : 'a) (n : int) (acc : 'a list) : 'a list = 
    match n with
    | 0 -> acc
    | n -> repeat' x (n-1) (x :: acc)
  in
  repeat' x n []*)
(* returns true if the list has at least one pair of duplicates *)
let rec exists_dup (xs : 'a list) : bool =
  match xs with
  | h :: t -> if List.exists ((=) h) t then true else exists_dup t
  | [] -> false
(* Returns true if s1 is non-empty and s2 is a prefix of s1 *)
let compare_sub (s1 : string) (s2 : string) : bool =
      let l2 = String.length s2 in
      let s1' = (try (String.sub s1 0 l2) with
                | Invalid_argument s -> "") in
      if (s1' <> "") && s1' = s2 then true else false 
let rec process_simplify (c : certif) : certif =
  match c with
  (* x_1 ^ ... ^ x_n <-> y *)
  | (i, AndsimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
       (* x_1 ^ ... F ... ^ x_n <-> F *)
       | [Eq ((And xs as lhs), (False as rhs))] when (List.exists ((=) False) xs) ->
         (* x ^ F <-> F
            LTR:
            -----asmp   -----------andp
            x ^ F       ~(x ^ F), F
            -----------------------res
                       F
         *)
         let a2bi = generate_id () in
         let ind = string_of_int (findi (term_eq False) xs) in
         let andpi = generate_id () in
         let a2b = [(andpi, AndpAST, [Not lhs; False], [], [ind]);
                    (generate_id (), ResoAST, [False], [a2bi; andpi], [])] in
         (*
            RTL:
             ---asmp             
              F
            --------weaken  ---false             
            F, x ^ F         ~F             
            ------------------res
                  x ^ F
         *)
         let b2ai = generate_id () in
         let wi = generate_id () in
         let fi = generate_id () in
         let b2a = [(wi, WeakenAST, [False; lhs], [b2ai], []);
                    (fi, FalsAST, [Not False], [], []);
                    (generate_id (), ResoAST, [lhs], [wi; fi], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 ^ ... x_i ... x_j ... ^ x_n <-> F, if x_i = ~x_j *)
       | [Eq ((And xs as lhs), (False as rhs))] when 
           (List.exists (fun x -> (List.exists (fun y -> is_neg y x) xs)) xs) ->
         (* x ^ ~x <-> F
            LTR:
                                          ------ass -------------andp
                                          x ^ ~x    ~(x ^ ~x), ~x
                                          -----------------------res  ---------imp_neg1
                                                    ~x                x -> F, x
            ------ass   ------------andp           ----------------------------res  ----------------imp_pos
            x ^ ~x      ~(x ^ ~x), x                           x -> F               ~(x -> F), ~x, F
            ------------------------res                        -------------------------------------res
                        x                                                        ~x, F
                        --------------------------------------------------------------res
                                                      F
         *)
         let a2bi = generate_id () in
         let x = List.find (fun x -> (List.exists (fun y -> y = Not x) xs)) xs in
         let x_ind = string_of_int (findi (term_eq x) xs) in
         let nx_ind = string_of_int (findi (term_eq (Not x)) xs) in
         let andpi1 = generate_id () in
         let resi1 = generate_id () in
         let impn1i = generate_id () in
         let resi2 = generate_id () in
         let imppi = generate_id () in
         let resi3 = generate_id () in
         let andpi2 = generate_id () in
         let resi4 = generate_id () in
         let a2b = [(andpi1, AndpAST, [Not lhs; Not x], [], [nx_ind]);
                    (resi1, ResoAST, [Not x], [a2bi; andpi1], []);
                    (impn1i, Impn1AST, [Imp [x; False]; x], [], []);
                    (resi2, ResoAST, [Imp [x; False]], [resi1; impn1i], []);
                    (imppi, ImppAST, [Not (Imp [x; False]); Not x; False], [], []);
                    (resi3, ResoAST, [Not x; False], [resi2; imppi], []);
                    (andpi2, AndpAST, [Not lhs; x], [], [x_ind]);
                    (resi4, ResoAST, [x], [a2bi; andpi2], []);
                    (generate_id (), ResoAST, [False], [resi3; resi4], [])] in
         (*
            RTL:
              --asmp
              F
            ---------weaken  ---false
            F, x ^ ~x         ~F
            ------------------res
                  x ^ ~x
         *)
         let b2ai = generate_id () in
         let wi = generate_id () in
         let fi = generate_id () in
         let b2a = [(wi, WeakenAST, [False; lhs], [b2ai], []);
                    (fi, FalsAST, [Not False], [], []);
                    (generate_id (), ResoAST, [lhs], [wi; fi], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* T ^ ... ^ T <-> T *)
       | [Eq ((And xs as lhs), (True as rhs))] when (List.for_all ((=) True) xs) ->
         (* T ^ T <-> T
            LTR:
            --true
            T
          *)          
         let a2b = [(generate_id (), TrueAST, [True], [], [])] in
         (*
            RTL: (note that and_neg would prove (T ^ T, ~T, ~T) but repeats
                  are removed in SMTCoq's representation)
            ---------andn   --asmp
            T ^ T, ~T          T     
            --------------------res
                    T ^ T
         *)
         let b2ai = generate_id () in
         let andn_id = generate_id () in
         let b2a = [(andn_id, AndnAST, [lhs; Not True], [], []);
                    (generate_id (), ResoAST, [lhs], [andn_id; b2ai], [])]
                     in
         (simplify_to_subproof i (generate_id ()) b2ai lhs rhs a2b b2a) @ process_simplify tl         
       (* x_1 ^ ... ^ x_n <-> x_1 ^ ... ^ x_n', RHS has all T removed *)
       | [Eq ((And xs as lhs), (And ys as rhs))] when ((List.exists ((=) True) xs) 
            && not (List.exists ((=) True) ys)) ->
          (* x ^ y ^ T <-> x ^ y
             LTR:
             ---------asmp  ---------------andp  ---------asmp ---------------andp
             x ^ y ^ T      ~(x ^ y ^ T), x      x ^ y ^ T     ~(x ^ y ^ T), y
             ------------------------------res   -----------------------------res    -------------andn
                             x                                 y                     x ^ y, ~x, ~y
                             ---------------------------------------------------------------------res
                                                            x ^ y
          *)
          let a2bi = generate_id () in
          (* for each y in to_uniq(ys),
               find index ind of first occurrence of y in xs and return
                1. (id1', AndpAST, [Not lhs; y], [], [ind]), (id2', ResoAST, [y], [id1'; a2bi], []), 
                2. id2'
                3. ~y
                where id1' and id2' are new ids *)
          let c1, proj_ids1, projnegl1 = List.fold_left 
            (fun (s, i, n) y ->
               let ind = string_of_int (findi (term_eq y) xs) in
               let id1' = generate_id () in
               let id2' = generate_id () in
               ((id1', AndpAST, [Not lhs; y], [], [ind]) :: (id2', ResoAST, [y], [a2bi; id1'], []) :: s,
                id2' :: i,
                Not y :: n))
              ([], [], []) (to_uniq ys) in
          let andni = generate_id () in
          let a2b = c1 @ 
                    [(andni, AndnAST, rhs :: projnegl1, [], []);
                     (generate_id (), ResoAST, [rhs], andni :: proj_ids1, [])] in
          (*
             RTL:
             -----asmp  -----------andp   -----asmp   -----------andp
             x ^ y      ~(x ^ y), x       x ^ y       ~(x ^ y), y    
             ----------------------res    -----------------------res ---true  ---------------------andn
                        x                             y               T       x ^ y ^ T, ~x, ~y, ~T
               ------------------------------------------------------------------------------------res
                                                      x ^ y ^ T
          *)
          let b2ai = generate_id () in
          let ti = generate_id () in
          (* for each x in to_uniq(xs) except x = T, 
              find index ind of first occurrence of x in ys and return
              1. (id1', AndpAST, [Not rhs; x], [], [ind]) :: (id2', ResoAST, [x], [b2ai; id1'], []])
              2. id2'
              3. ~x
              where id1' and id2' are new ids *)
          let c2, proj_ids2, projnegl2 = List.fold_left 
            (fun (s, i, n) x ->
              if x = True then (s, i, n)
              else
                let ind = string_of_int (findi (term_eq x) ys) in
                let id1' = generate_id () in
                let id2' = generate_id () in
                ((id1', AndpAST, [Not rhs; x], [], [ind]) :: (id2', ResoAST, [x], [b2ai; id1'], []) :: s,
                 id2' :: i,
                 Not x :: n))
            ([], [], []) (to_uniq xs) in
          let andni = generate_id () in
          let b2a = c2 @
                    [(ti, TrueAST, [True], [], []);
                     (andni, AndnAST, lhs :: Not True :: projnegl2, [], []);
                     (generate_id (), ResoAST, [lhs], andni :: ti :: proj_ids2, [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 ^ ... ^ x_n <-> x_1 ^ ... ^ x_n', RHS has all repeated literals removed *)
       | [Eq ((And xs as lhs), (And ys as rhs))] when (exists_dup xs) && not (exists_dup ys) ->
          (* x ^ y ^ x <-> x ^ y
             LTR:
             ---------asmp ----------------andp ---------asmp  ----------------andp
             x ^ y ^ x     ~(x ^ y ^ x), x      x ^ y ^ x      ~(x ^ y ^ x), y    
             ------------------------------res  -------------------------------res    -------------andn
                           x                                   y                      x ^ y, ~x, ~y
                           ------------------------------------------------------------------------res
                                                            x ^ y
          *)
          let a2bi = generate_id () in
          (* for each y in to_uniq(ys),
               find index ind of first occurrence of y in xs and return
                1. (id1', AndpAST, [Not lhs; y], [], [ind]) :: (id2', ResoAST, [y], [a2bi; id1'], [])
                2. id2'
                3. ~y 
                where id1' and id2' are new ids *)
          let c1, proj_ids1, projnegl1 = List.fold_left
            (fun (s, i, n) y -> 
              let ind = string_of_int (findi (term_eq y) xs) in
              let id1' = generate_id () in
              let id2' = generate_id () in
              ((id1', AndpAST, [Not lhs; y], [], [ind]) :: (id2', ResoAST, [y], [a2bi; id1'], []) :: s,
               id2' :: i,
               Not y :: n))
              ([], [], []) (to_uniq ys) in
          let andni = generate_id () in
          let a2b = c1 @
                    [(andni, AndnAST, rhs :: projnegl1, [], []);
                     (generate_id (), ResoAST, [rhs], andni :: proj_ids1, [])] in
          (*
             RTL: Note that andn would project the repeated literals (another ~x here), but 
                  SMTCoq's representation would remove repeats
             -----asmp  -------------andp -----asmp   -------------andp
             x ^ y       ~(x ^ y), x      x ^ y        ~(x ^ y), y    
             ------------------------res  -------------------------res  -----------------andn
                        x                             y                 x ^ y ^ x, ~x, ~y
                        -----------------------------------------------------------------res
                                                      x ^ y ^ x
          *)
          let b2ai = generate_id () in
          (* for each y in to_uniq(ys)
               find index ind of first occurrence of y in ys and return
                1. (id1', AndpAST, [Not rhs; y], [], [ind]) :: (id2', ResoAST, [y], [b2ai; id1'], [])
                2. id2'
                3. ~x 
                where id1' and id2' are new ids *)
          let c2, proj_ids2, projnegl2 = List.fold_left 
            (fun (s, i, n) y ->
              let ind = string_of_int (findi (term_eq y) ys) in
              let id1' = generate_id () in
              let id2' = generate_id () in
                ((id1', AndpAST, [Not rhs; y], [], [ind]) :: (id2', ResoAST, [y], [b2ai; id1'], []) :: s,
                 id2' :: i,
                 Not y :: n))
            ([], [], []) (to_uniq ys) in
          let andni = generate_id () in
          let b2a = c2 @
                    [(andni, AndnAST, lhs :: projnegl2, [], []);
                     (generate_id (), ResoAST, [lhs], andni :: proj_ids2, [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 ^ ... ^ x_n <-> x_i, RHS has all repeated literals removed (singleton `and` case) *)
       | [Eq ((And xs as lhs), x)] ->
         (* x ^ ... ^ x <-> x
            LTR:
            -----------asmp ----------------andp
            x ^ ... ^ x     ~(x ^ ... ^ x), x   
            ------------------------------res
                          x
         *)
         let a2bi = generate_id () in
         let andpi = generate_id () in
         let a2b = [(andpi, AndpAST, [Not lhs; x], [], ["0"]);
                    (generate_id (), ResoAST, [x], [a2bi; andpi], [])] in
         (*
            RTL: Note that andn would project the repeated literals (another ~x here), but 
                 SMTCoq's representation would remove repeats
            ---asmp  ---------------andn
             x       x ^ ... ^ x, ~x    
            ------------------------res 
                  x ^ ... ^ x
         *)
         let b2ai = generate_id () in
         let andni = generate_id () in
         let b2a = [(andni, AndnAST, [lhs; Not x], [], []);
                    (generate_id (), ResoAST, [lhs], [b2ai; andni], [])] in
         (simplify_to_subproof i a2bi b2ai lhs x a2b b2a) @ process_simplify tl
       | [Eq _] -> raise (Debug ("| process_simplify: unexpected form of equivalence for and_simplify at id "^i^" |"))
       | _ -> raise (Debug ("| process_simplify: expecting and_simplify to derive a singleton equivalence at id "^i^" |")))
  (* x_1 v ... v x_n <-> y *)
  | (i, OrsimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
       (* x_1 v ... T ... x_n <-> T *)
       | [Eq ((Or xs as lhs), (True as rhs))] when (List.exists ((=) True) xs) ->
         (* x v T <-> T
            LTR:
            --true
            T
         *)
         let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
         let orn_id = generate_id () in
         (*
            RTL:
            --asmp   -----------orn
            T        (x v T), ~T
            --------------------res
                   x v T
         *)
         let b2ai = generate_id () in
         let orn_a = string_of_int (findi (term_eq True) xs) in
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
         *)
         let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
         (*
            RTL:
            --------------orn    -------------orn
            (x v ~x), ~x         (x v ~x), ~~x
            ----------------------------------res
                          x v ~x
         *)
         let orn_id1 = generate_id () in
         let orn_id2 = generate_id () in
         let x = List.find (fun x -> (List.exists (fun y -> y = Not x) xs)) xs in
         let x_id = string_of_int (findi (term_eq x) xs) in
         let nx_id = string_of_int (findi (term_eq (Not x)) xs) in
         let b2a = [(orn_id1, OrnAST, [lhs; Not x], [], [x_id]);
                    (orn_id2, OrnAST, [lhs; x], [], [nx_id]);
                    (generate_id (), ResoAST, [lhs], [orn_id1; orn_id2], [])] in
         (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl      
       (* F v ... v F <-> F *)
       | [Eq ((Or xs as lhs), (False as rhs))] when (List.for_all ((=) False) xs) ->
          (* F v F <-> F
             LTR: (Note that or_pos would derive another F but SMTCoq would only store one F)
             -----asmp  -----------orp
             F v F      ~(F v F), F
             ----------------------res
                        F
          *)
           let a2bi = generate_id () in
           let orp_id = generate_id () in
           let a2b = [(orp_id, OrpAST, [Not lhs; False], [],[]);
                      (generate_id (), ResoAST, [rhs], [orp_id; a2bi], [])] in
          (*
             RTL:
             --asmp   ---------orn
             F        F v F, ~F
             ------------------res
                    F v F
          *)
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
             ---------asmp  ---------------------orp  --false
             x v y v F      ~(x v y v F), x, y, F     ~F
             --------------------------------------------res  ---------orn   ---------orn
                                 x, y                          x v y, ~x      x v y, ~y
                                 ------------------------------------------------------res
                                                         x v y
          *)
           let a2bi = generate_id () in
           let orpi = generate_id () in
           let resi = generate_id () in
           let fi = generate_id () in
           (* for each y in to_uniq(ys), return
              find index ind of first occurrence of y in ys and return
              1. fresh id i'
              2. (i', OrnAST, [rhs; Not y], [], [ind]) *)
           let ornis, orns = List.fold_left
            (fun (i, r) y ->
               let i' = generate_id () in
               let ind = string_of_int (findi (term_eq y) ys) in
               i' :: i,
               (i', OrnAST, [rhs; Not y], [], [ind]) :: r)
            ([], []) (to_uniq ys) in
            let a2b = [(orpi, OrpAST, Not lhs :: xs, [], []);
                       (fi, FalsAST, [Not False], [], []);
                       (resi, ResoAST, xs, [a2bi; orpi; fi], [])] @ 
                      orns @
                      [(generate_id (), ResoAST, [rhs], resi :: ornis, [])] in
          (*
            RTL:
            -----asmp   --------------orp
            x v y       ~(x v y), x, y
            --------------------------res   ---------------orn   ---------------orn
                        x,y                 (x v y v F), ~x      (x v y v F), ~y
                        --------------------------------------------------------res
                                                   x v y v F
          *)
           let b2ai = generate_id () in
           let orpi = generate_id () in
           let resi = generate_id () in
           (* for each y in to_uniq(ys),
                find index ind of first occurrence of y in xs and return
                 1. (id', OrnAST, [lhs; ~y], [], [ind]), where id' is a new id
                 2. id' *)
           let c, proj_ids = List.fold_left 
             (fun (s, i) y -> 
               let ind = string_of_int (findi (term_eq y) xs) in
               let id' = generate_id () in
               ((id', OrnAST, [lhs; Not y], [], [ind]) :: s,
                id' :: i))
             ([], []) (to_uniq ys) in
           let b2a = [(orpi, OrpAST, Not rhs :: (to_uniq ys), [], []);
                      (resi, ResoAST, ys, [b2ai; orpi], [])] @
                     c @
                     [(generate_id (), ResoAST, [lhs], resi :: proj_ids, [])] in
           (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x_1 v ... v x_n <-> x_1 v ... x_n', RHS has all repeated literals removed *)
       | [Eq ((Or xs as lhs), (Or ys as rhs))] when (exists_dup xs) && not (exists_dup ys) ->
          (* x v y v x <-> x v y
             LTR: Duplicates are removed in orp by SMTCoq's representation
             ---------asmp ------------------orp
             x v y v x     ~(x v y v x), x, y
             --------------------------------res   ---------orn   ---------orn
                            x, y                   x v y, ~x      x v y, ~y
                            -----------------------------------------------res
                                                x v y
          *)
           let a2bi = generate_id () in
           let orpi = generate_id () in
           let resi = generate_id () in
           (* for each y in to_uniq(ys),
                find index ind of first occurrence of y in ys and return
                 1. (id', OrnAST, [rhs; ~y], [], [ind]), where id' is a new id
                 2. id' *)
                 let c, proj_ids = List.fold_left 
                 (fun (s, i) y -> 
                   let ind = string_of_int (findi (term_eq y) xs) in
                   let id' = generate_id () in
                   ((id', OrnAST, [rhs; Not y], [], [ind]) :: s,
                    id' :: i))
                 ([], []) (to_uniq ys) in
           let a2b = [(orpi, OrpAST, Not lhs :: ys, [], []);
                      (resi, ResoAST, ys, [a2bi; orpi], [])] @
                     c @
                     [(generate_id (), ResoAST, [lhs], resi :: proj_ids, [])] in
          (*
             RTL:
             -----asmp  --------------orp
             x v y      ~(x v y), x, y
             -------------------------res ---------------orn   ---------------orn
                        x,y               (x v y v x), ~x      (x v y v x), ~y
                        ------------------------------------------------------res
                                             x v y v x
          *)           
           let b2ai = generate_id () in
           let orpi = generate_id () in
           let resi = generate_id () in
           (* for each y in ys,
               find index ind of first occurrence of y in xs and return
                1. (id', OrnAST, [lhs; Not y], [], [ind]), where id' is a new id
                2. id' *)
           let c, proj_ids = List.fold_left 
            (fun (s,i) y -> 
              let ind = string_of_int (findi (term_eq y) xs) in
              let id' = generate_id () in
              ((id', OrnAST, [lhs; Not y], [], [ind]) :: s,
               id' :: i))
              ([], []) ys in
           let b2a = [(orpi, OrpAST, Not rhs :: ys, [], []);
                      (resi, ResoAST, ys, [b2ai; orpi], [])] @ 
                     c @
                     [(generate_id (), ResoAST, [lhs], resi :: proj_ids, [])] in 
           (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       | [Eq _] -> raise (Debug ("| process_simplify: unexpected form of equivalence for or_simplify at id "^i^" |"))
       | _ -> raise (Debug ("| process_simplify: expecting or_simplify to derive a singleton equivalence at id "^i^" |")))
  (* ~x <-> y *)
  | (i, NotsimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
       (* ~F <-> T *)
          | [Eq ((Not False as lhs), (True as rhs))] ->
          (*
             LTR:
             --true
             T
          *)
          let a2b = [(generate_id (), TrueAST, [True], [], [])] in
          (*
             RTL:
             --false
             ~F
          *)          
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
          (*
             RTL:
               ---asmp
                F
             --------weaken   ------false
             F, ~T             ~F
             ------------------------res
                         ~T
          *)
          let b2ai = generate_id () in
          let weaki = generate_id () in
          let fi = generate_id () in
          let b2a = [(weaki, WeakenAST, [False; Not True], [b2ai], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [Not True], [weaki; fi], [])] in         
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ~~x <-> x *)
       | [Eq (Not (Not x), y)] when x = y -> 
         (* Since SMTCoq implicitly removes double negations, we replace this by a derivation of x = x *)
          let eqn1i = generate_id () in
          let eqn2i = generate_id () in
          (eqn1i, Equn1AST, [Eq (x, x); Not x], [], []) ::
          (eqn2i, Equn2AST, [Eq (x, x); x], [], []) ::
          (i, ResoAST, [Eq (x, x)], [eqn1i; eqn2i], []) :: process_simplify tl
       (* | [Eq _] -> (i, NotsimpAST, cl, p, a) :: process_simplify tl *)
       | _ -> raise (Debug ("| process_simplify: expecting not_simplify to derive a singleton equivalence at id "^i^" |")))
  (* (x -> y) <-> z *)
  | (i, ImpsimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
       (* (~x -> ~y) <-> (y -> x) *)
       | [Eq ((Imp [Not x; Not y] as lhs), (Imp [b; a] as rhs))] when (x = a && y = b) ->
          (*
             LTR:
             --------asmp   --------------------impp
             ~x -> ~y       ~(~x -> ~y), ~~x, ~y
             -----------------------------------res   ---------impn1   -----------impn2
                           ~~x, ~y                    y -> x, y        y -> x, ~x
                           ------------------------------------------------------res
                                                   y -> x
          *)
          let a2bi = generate_id () in
          let imppi1 = generate_id () in
          let resi1 = generate_id () in
          let impn1i1 = generate_id () in
          let impn2i1 = generate_id () in
          let a2b = [(imppi1, ImppAST, [Not lhs; x; Not y], [], []);
                     (resi1, ResoAST, [x; Not y], [a2bi; imppi1], []);
                     (impn1i1, Impn1AST, [rhs; y], [], []);
                     (impn2i1, Impn2AST, [rhs; Not x], [], []);
                     (generate_id (), ResoAST, [rhs], [resi1; impn1i1; impn2i1], [])] in
          (*
             RTL:
             ------asmp ----------------impp
             y -> x     ~(y -> x), ~y, x
             ---------------------------res     ------------impn1  -------------impn2
                        ~y, x                   ~x -> ~y, ~x       ~x -> ~y, ~~y
                        --------------------------------------------------------res
                                                ~x -> ~y
          *)
          let b2ai = generate_id () in
          let imppi2 = generate_id () in
          let resi2 = generate_id () in
          let impn1i2 = generate_id () in
          let impn2i2 = generate_id () in
          let b2a = [(imppi2, ImppAST, [Not rhs; Not y; x], [], []);
                     (resi2, ResoAST, [Not y; x], [b2ai; imppi2], []);
                     (impn1i2, Impn1AST, [lhs; Not x], [], []);
                     (impn2i2, Impn2AST, [lhs; y], [], []);
                     (generate_id (), ResoAST, [lhs], [resi2; impn1i2; impn2i2], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (F -> x) <-> T *)
       | [Eq ((Imp [False; x] as lhs), (True as rhs))] ->
          (*
             LTR:
             --true
             T
          *)
          let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
          (*
             RTL:
             ---------impn1  --false
             F -> x, F        ~F
             ---------------------res
                     F -> x
          *)
          let impni = generate_id () in
          let fi = generate_id () in
          let b2a = [(impni, Impn1AST, [Imp [False; x]; False], [], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [Imp [False; x]], [impni; fi], [])] in
          (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl
       (* (x -> T) <-> T *)
       | [Eq ((Imp [x; True] as lhs), (True as rhs))] ->
          (*
             LTR:
             --true
             T
          *)
          let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
          (*
             RTL:
             --asmp   ----------impn2
             T        x -> T, ~T
             -------------------res
                   x -> T
          *)
          let b2ai = generate_id () in
          let impni = generate_id () in
          let b2a = [(impni, Impn2AST, [lhs; Not True], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai;impni], [])] in
          (simplify_to_subproof i (generate_id ()) b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (T -> x) <-> x *)
       | [Eq ((Imp [True; x] as lhs), (a as rhs))] when (x = a) ->
          (*
             LTR:
             ------asmp -----------------impp
             T -> x     ~(T -> x), ~T, x
             ---------------------------res   --true
                        ~T, x                  T
                        ------------------------res
                                    x
          *)
          let a2bi = generate_id () in
          let imppi = generate_id () in
          let resi = generate_id () in
          let ti = generate_id () in
          let a2b = [(imppi, ImppAST, [Not lhs; Not True; x], [], []);
                     (resi, ResoAST, [Not True; x], [a2bi; imppi], []);
                     (ti, TrueAST, [True], [], []);
                     (generate_id (), ResoAST, [rhs], [resi; ti], [])] in
          (*
             RTL:
             --asmp   -----------impn2
             x        T -> x, ~x
             -------------------res
                    T -> x
          *)
          let b2ai = generate_id () in
          let impn2i = generate_id () in
          let b2a = [(impn2i, Impn2AST, [lhs; Not x], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai; impn2i], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x -> F) <-> ~x *)
       | [Eq ((Imp [x;False] as lhs), (Not a as rhs))] when (x = a) ->
          (*
             LTR:
             ------asmp ----------------impp
             x -> F     ~(x -> F), ~x, F
             ---------------------------res  --false
                        ~x, F                ~F
                        -----------------------res
                                   ~x
          *)
          let a2bi = generate_id () in
          let imppi = generate_id () in
          let resi = generate_id () in
          let fi = generate_id () in
          let a2b = [(imppi, ImppAST, [Not lhs; Not x; False], [], []);
                     (resi, ResoAST, [Not x; False], [a2bi; imppi], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [rhs], [resi; fi], [])] in
          (*
             RTL:
             --asmp   ---------impn1
             ~x       x -> F, x
             ------------------res
                  x -> F
          *)
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
          *)
          let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
          (*
             RTL:
             ---------impn1  ----------impn2
             x -> x, x       x -> x, ~x
             --------------------------res
                         x -> x
          *)
          let impn1i = generate_id () in
          let impn2i = generate_id () in
          let b2a = [(impn1i, Impn1AST, [Imp [x;x]; x], [], []);
                     (impn2i, Impn2AST, [Imp [x;x]; Not x], [], []);
                     (generate_id (), ResoAST, [lhs], [impn1i;impn2i], [])] in
          (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl
       (* (~x -> x) <-> x *)
       | [Eq ((Imp [Not x;a] as lhs), (b as rhs))] when (x = a && x = b) ->
          (*
             LTR: (SMTCoq will remove double negations and duplicates)
             -------asmp  ------------------impp
             ~x -> x      ~(~x -> x), ~~x, x
             -------------------------------res
                            x
          *)
          let a2bi = generate_id () in
          let imppi = generate_id () in
          let a2b = [(imppi, ImppAST, [Not lhs; x; x], [], []);
                     (generate_id (), ResoAST, [rhs], [a2bi;imppi],[])] in
          (*
             RTL:
             --asmp -----------impn1
             x      ~x -> x, ~x
             ------------------res
                  ~x -> x
          *)
          let b2ai = generate_id () in
          let impni = generate_id () in
          let b2a = [(impni, Impn1AST, [lhs; Not x], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai;impni], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x -> ~x) <-> ~x *)
       | [Eq ((Imp [x; Not a] as lhs), (Not b as rhs))] when (x = a && x = b) ->
          (*
             LTR: (SMTCoq will remove duplicates)
             -------asmp  ------------------impp
             x -> ~x      ~(x -> ~x), ~x, ~x
             -------------------------------res
                           ~x
          *)
          let a2bi = generate_id () in
          let imppi = generate_id () in
          let a2b = [(imppi, ImppAST, [Not lhs; Not x; Not x], [], []);
                     (generate_id (), ResoAST, [rhs], [a2bi; imppi], [])] in
          (*
             RTL:
             --asmp   ----------impn1
             ~x       x -> ~x, x
             -------------------res
                  x -> ~x
          *)
          let b2ai = generate_id () in
          let impn1i = generate_id () in
          let b2a = [(impn1i, Impn1AST, [lhs; x], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai; impn1i], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       | [Eq _] -> raise (Debug ("| process_simplify: unexpected form of equivalence for implies_simplify at id "^i^" |"))
       | _ -> raise (Debug ("| process_simplify: expecting implies_simplify to derive a singleton equivalence at id "^i^" |")))
  (* (x <-> y) <-> z *)
  | (i, EqsimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
       (* (~x <-> ~y) <-> (x <-> y) *)
       | [Eq ((Eq (Not x, Not y) as lhs),(Eq (a, b) as rhs))] when x = a && y = b ->
          (*
             LTR:
             -----------------eqn1  	----------------------eqp1	-----------------eqn2	----------------------eqp2
             (x <-> y), ~x, ~y		   ~(~x <-> ~y), ~x, ~~y		    (x <-> y), x, y			  ~(~x <-> ~y), ~~x, ~y
             ---------------------------------------------res	    -------------------------------------------res	-----------asmp
             		    (x <-> y), ~x, ~(~x <-> ~y)							              (x <-> y), x, ~(~x <-> ~y)					     (~x <-> ~y)
             		    --------------------------------------------------------------------------------------------------------res
             														                        (x <-> y)
          *)
          let a2bi = generate_id () in
          let eqn1i = generate_id () in
          let eqp1i = generate_id () in
          let resi1 = generate_id () in
          let eqn2i = generate_id () in
          let eqp2i = generate_id () in
          let resi2 = generate_id () in
          let a2b = [(eqn1i, Equn1AST, [rhs; Not x; Not y], [], []);
                     (eqp1i, Equp1AST, [Not lhs; Not x; y], [], []);
                     (resi1, ResoAST, [lhs; Not x; rhs], [eqn1i; eqp1i], []);
                     (eqn2i, Equn2AST, [rhs; x; y], [], []);
                     (eqp2i, Equp2AST, [Not lhs; x; Not y], [], []);
                     (resi2, ResoAST, [lhs; x; rhs], [eqn2i; eqp2i], []);
                     (generate_id (), ResoAST, [rhs], [resi1; resi2; a2bi], [])] in
          (*
             RTL:
             ---------------------eqn1	-----------------eqp1	--------------------eqn2	-----------------eqp2
             (~x <-> ~y), ~~x, ~~y		~(x <-> y), x, ~y		   (~x <-> ~y), ~x, ~y			~(x <-> y), ~x, y
             ---------------------------------------------res	---------------------------------------------res	---------asmp
             		        (~x <-> ~y), x, ~(x <-> y)							        (~x <-> ~y), ~x, ~(x <-> y)					     (x <-> y)
             		        --------------------------------------------------------------------------------------------------res
             														                          (~x <-> ~y)
          *)
          let b2ai = generate_id () in
          let eqn1i = generate_id () in
          let eqp1i = generate_id () in
          let resi1 = generate_id () in
          let eqn2i = generate_id () in
          let eqp2i = generate_id () in
          let resi2 = generate_id () in
          let b2a = [(eqn1i, Equn1AST, [lhs; x; y], [], []);
                     (eqp1i, Equp1AST, [Not rhs; x; Not y], [], []);
                     (resi1, ResoAST, [lhs; x; rhs], [eqn1i; eqp1i], []);
                     (eqn2i, Equn2AST, [lhs; Not x; Not y], [], []);
                     (eqp2i, Equp2AST, [Not rhs; Not x; y], [], []);
                     (resi2, ResoAST, [lhs; Not x; rhs], [eqn2i; eqp2i], []);
                     (generate_id (), ResoAST, [lhs], [resi1; resi2; b2ai], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x <-> x) <-> T *)
       | [Eq ((Eq (x, a) as lhs), (True as rhs))]  when x = a ->
          (*
             LTR:
             ---true
              T
          *)
          let a2b = [(generate_id (), TrueAST, [True], [], [])] in
          (*
             RTL:
             ---------------eqn1  -------------eqn2
             x <-> x, ~x, ~x      x <-> x, x, x
             ----------------------------------res
                            x <-> x
          *)
          let eqn1i = generate_id () in
          let eqn2i = generate_id () in
          let b2a = [(eqn1i, Equn1AST, [lhs; Not x; Not x], [], []);
                     (eqn2i, Equn2AST, [lhs; x; x], [], []);
                     (generate_id (), ResoAST, [lhs], [eqn1i; eqn2i], [])] in
          (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl
       (* (x <-> ~x) <-> F *)
       | [Eq ((Eq (x, Not a) as lhs), (False as rhs))] when x = a ->
          (*
             LTR:
             -------------------eqp2  ---------impn1  ----------------impp   -------------------eqp1    --------asmp
             ~(x <-> ~x), ~x, ~x      x -> F, x       ~(x -> F), ~x, F       ~(x <-> ~x), x, ~~x        x <-> ~x
             ---------------------------------------------------------------------------------------------------res
                                                                F
          *)
          let a2bi = generate_id () in
          let eqp2i = generate_id () in
          let impn1i = generate_id () in
          let imppi = generate_id () in
          let eqp1i = generate_id () in
          let a2b = [(eqp2i, Equp2AST, [Not lhs; Not x; Not x], [], []);
                     (impn1i, Impn1AST, [Imp [x; False]; x], [], []);
                     (imppi, ImppAST, [Not (Imp [x; False]); Not x; False], [], []);
                     (eqp1i, Equp1AST, [Not lhs; x; x], [], []);
                     (generate_id (), ResoAST, [rhs], [eqp2i; impn1i; imppi; eqp1i; a2bi], [])] in
          (*
             RTL: 
                ---asmp               
                 F
            -----------weaken  ---false
            F, x <-> ~x           ~F
            ------------------------res
                    x <-> ~x
          *)
          let b2ai = generate_id () in
          let wi = generate_id () in
          let fi = generate_id () in
          let b2a = [(wi, WeakenAST, [False; lhs], [b2ai], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [lhs], [wi; fi], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (~x <-> x) <-> F *)
       | [Eq ((Eq (Not x, a) as lhs), (False as rhs))] when x = a ->
          (*
             LTR:
             -------------------eqp1  ---------impn1  ----------------impp ---------------------eqp2  --------asmp
             ~(~x <-> x), ~x, ~x      x -> F, x       ~(x -> F), ~x, F     ~(~x <-> x), ~~x, x        x <-> ~x
             --------------------------------------------------------------------------------------------------
                                                            F
          *)
          let a2bi = generate_id () in
          let eqp1i = generate_id () in
          let impn1i = generate_id () in
          let imppi = generate_id () in
          let eqp2i = generate_id () in
          let a2b = [(eqp1i, Equp1AST, [Not lhs; Not x; Not x], [], []);
                     (impn1i, Impn1AST, [Imp [x; False]; x], [], []);
                     (imppi, ImppAST, [Not (Imp [x; False]); Not x; False], [], []);
                     (eqp2i, Equp2AST, [Not lhs; x; x], [], []);
                     (generate_id (), ResoAST, [rhs], [eqp1i; impn1i; imppi; eqp2i; a2bi], [])] in
          (*
             RTL:
                ---asmp               
                 F
            -----------weaken  ---false
            F, ~x <-> x           ~F
            ------------------------res
                    ~x <-> x
          *)                     
          let b2ai = generate_id () in
          let wi = generate_id () in
          let fi = generate_id () in
          let b2a = [(wi, WeakenAST, [False; lhs], [b2ai], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [lhs], [wi; fi], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (T <-> x) <-> x *)
       | [Eq ((Eq (True, x) as lhs), (a as rhs))] when x = a ->
          (*
             LTR:
             -------asmp  -----------------eqp2 ---true
             T <-> x      ~(T <-> x), ~T, x      T
             -------------------------------------res
                               x
          *)
          let a2bi = generate_id () in
          let eqp2i = generate_id () in
          let ti = generate_id () in
          let a2b = [(eqp2i, Equp2AST, [Not lhs; Not True; x], [], []);
                     (ti, TrueAST, [True], [], []);
                     (generate_id (), ResoAST, [rhs], [a2bi; eqp2i; ti], [])] in
          (*
             RTL:
             --asmp  -----------------eqn1 ---true
             x       (T <-> x), ~T, ~x      T
             --------------------------------res
                          T <-> x
          *)
          let b2ai = generate_id () in
          let eqn1i = generate_id () in
          let ti = generate_id () in
          let b2a = [(eqn1i, Equn1AST, [lhs; Not True; Not x], [], []);
                     (ti, TrueAST, [True], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai; eqn1i; ti], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x <-> T) <-> x *)
       | [Eq ((Eq (x, True) as lhs), (a as rhs))] when x = a ->
          (*
             LTR:
             -------asmp  -----------------eqp1 ---true
             x <-> T      ~(x <-> T), x, ~T      T
             -------------------------------------res
                               x
          *)
          let a2bi = generate_id () in
          let eqp1i = generate_id () in
          let ti = generate_id () in
          let a2b = [(eqp1i, Equp1AST, [Not lhs; x; Not True], [], []);
                     (ti, TrueAST, [True], [], []);
                     (generate_id (), ResoAST, [rhs], [a2bi; eqp1i; ti], [])] in
          (*
             RTL:
             --asmp  -----------------eqn1 ---true
             x       (x <-> T), ~x, ~T      T
             --------------------------------res
                          x <-> T
          *)
          let b2ai = generate_id () in
          let eqn1i = generate_id () in
          let ti = generate_id () in
          let b2a = [(eqn1i, Equn1AST, [lhs; Not x; Not True], [], []);
                     (ti, TrueAST, [True], [], []);
                     (generate_id (), ResoAST, [rhs], [b2ai; eqn1i; ti], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (F <-> x) <-> ~x *)
       | [Eq ((Eq (False, x) as lhs), (Not a as rhs))] when x = a ->
          (*
             LTR:
             -------asmp  -----------------eqp1 ---false
             F <-> x      ~(F <-> x), F, ~x      ~F
             -------------------------------------res
                               ~x
          *)
          let a2bi = generate_id () in
          let eqpi1 = generate_id () in
          let fi = generate_id () in
          let a2b = [(eqpi1, Equp1AST, [Not lhs; Not x], [], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [rhs], [a2bi; eqpi1; fi], [])] in
          (*
             RTL:
             --asmp  -----------------eqn2 ---false
             ~x      (F <-> x), F, x        ~F
             --------------------------------res
                          F <-> x
          *)
          let b2ai = generate_id () in
          let eqn2i = generate_id () in
          let fi = generate_id () in
          let b2a = [(eqn2i, Equn2AST, [lhs; False; x], [], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai; eqn2i; fi], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x <-> F) <-> ~x *)
       | [Eq ((Eq (x, False) as lhs), (Not a as rhs))] when x = a ->
          (*
             LTR:
             -------asmp  -----------------eqp2 ---false
             x <-> F      ~(x <-> F), ~x, F      ~F
             -------------------------------------res
                               ~x
          *)
          let a2bi = generate_id () in
          let eqp2i = generate_id () in
          let fi = generate_id () in
          let a2b = [(eqp2i, Equp2AST, [Not lhs; Not x; False], [], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [rhs], [a2bi; eqp2i; fi], [])] in
          (*
             RTL:
             --asmp  -----------------eqn2 ---false
             ~x      (x <-> F), x, F        ~F
             --------------------------------res
                          x <-> F
          *)
          let b2ai = generate_id () in
          let eqn2i = generate_id () in
          let fi = generate_id () in
          let b2a = [(eqn2i, Equn2AST, [lhs; x; False], [], []);
                     (fi, FalsAST, [Not False], [], []);
                     (generate_id (), ResoAST, [lhs], [b2ai; eqn2i; fi], [])] in
          (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       | [Eq _] -> raise (Debug ("| process_simplify: unexpected form of equivalence for equiv_simplify at id "^i^" |"))
       | _ -> raise (Debug ("| process_simplify: expecting equiv_simplify to derive a singleton equivalence at id "^i^" |")))
  (* ite c x y <-> z *)
  | (i, ItesimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
       (* ite T x y <-> x *)
       | [Eq ((Ite [True; x; y] as lhs), (a as rhs))] when x = a ->
         (*
             LTR:
             --------------------itep2  ---------asmp  --T
             ~(ite T x y), ~T, x        ite T x y      T
             -------------------------------------------res
                                  x
         *)
         let a2bi = generate_id () in
         let itep2i = generate_id () in
         let ti = generate_id () in
         let a2b = [(itep2i, Itep2AST, [Not lhs; Not True; x], [], []);
                    (ti, TrueAST, [True], [], []);
                    (generate_id (), ResoAST, [rhs], [itep2i; a2bi; ti], [])] in
         (*
             RTL:
             -----------------iten2  --T  --asmp
             ite T x y, ~T, ~x       T    x
             ------------------------------res
                       ite T x y
         *)
         let b2ai = generate_id () in
         let iten2i = generate_id () in
         let ti = generate_id () in
         let b2a = [(iten2i, Iten2AST, [lhs; Not True; Not x], [], []);
                    (ti, TrueAST, [True], [], []);
                    (generate_id (), ResoAST, [lhs], [iten2i; ti; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite F x y <-> y *)
       | [Eq ((Ite [False; x; y] as lhs), (b as rhs))] when y = b ->
         (*
             LTR:
             --------------------itep1  ---------asmp  --F
             ~(ite F x y), F, y         ite F x y      ~F 
             --------------------------------------------res
                                 y
         *)
         let a2bi = generate_id () in
         let itep1i = generate_id () in
         let fi = generate_id () in
         let a2b = [(itep1i, Itep1AST, [Not lhs; y], [], []);
                    (fi, FalsAST, [Not False], [], []);
                    (generate_id (), ResoAST, [rhs], [itep1i; a2bi; fi], [])] in
         (*
             RTL:
             -----------------iten1  --F  --asmp
             ite F x y, F, ~y        ~F   y
             ------------------------------res
                       ite F x y
         *)
         let b2ai = generate_id () in
         let iten1i = generate_id () in
         let fi = generate_id () in
         let b2a = [(iten1i, Iten1AST, [lhs; False; Not y], [], []);
                    (fi, FalsAST, [Not False], [], []);
                    (generate_id (), ResoAST, [lhs], [iten1i; fi; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c x x <-> x *)
       | [Eq ((Ite [c; x; a] as lhs), (m as rhs))] when x = a && x = m ->
         (*
             LTR:
             ------------------itep1  -------------------itep2  ---------asmp
             ~(ite c x x), c, x       ~(ite c x x), ~c, x       ite c x x
             ------------------------------------------------------------
                                          x
         *)
         let a2bi = generate_id () in
         let itep1i = generate_id () in
         let itep2i = generate_id () in
         let a2b = [(itep1i, Itep1AST, [Not lhs; c; x], [], []);
                    (itep2i, Itep2AST, [Not lhs; Not x; x], [], []);
                    (generate_id (), ResoAST, [rhs], [itep1i; itep2i; a2bi], [])] in
         (*                                 
             RTL:
             ----------------iten1  -----------------iten2  --asmp
             ite c x x, c, ~x       ite c x x, ~c, ~x        x
             -------------------------------------------------
                                 ite c x x
         *)
         let b2ai = generate_id () in
         let iten1i = generate_id () in
         let iten2i = generate_id () in
         let b2a = [(iten1i, Iten1AST, [lhs; c; Not x], [], []);
                     (iten2i, Iten2AST, [lhs; Not x; Not x], [], []);
                     (generate_id (), ResoAST, [lhs], [iten1i; iten2i; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite ~c x y <-> ite c y x *)
       | [Eq ((Ite [Not c; x; y] as lhs), (Ite [c'; b; a] as rhs))] when c = c' && x = a && y = b ->
         (*
             LTR:
             ------------------iten1  ---------------------itep2  --------------------itep1  -----------------iten2
              ite c y x, c, ~x        ~(ite ~c x y), ~~c, x       ~(ite ~c x y), ~c, y       ite c y x, ~c, ~y   
              ---------------------------------------------res    ---------------------------------------------res  ----------asmp
                      ite c y x, c, ~(ite ~c x y)                         ~(ite ~c x y), ~c, ite c y x              ite ~c x y
                      --------------------------------------------------------------------------------------------------------res   
                                                                     ite c y x
         *)
         let a2bi = generate_id () in
         let iten1i = generate_id () in
         let itep2i = generate_id () in
         let resi1 = generate_id () in
         let itep1i = generate_id () in
         let iten2i = generate_id () in
         let resi2 = generate_id () in
         let a2b = [(iten1i, Iten1AST, [rhs; Not x], [], []);
                    (itep2i, Itep2AST, [Not lhs; c; x], [], []);
                    (resi1, ResoAST, [rhs; c; Not lhs], [iten1i; itep2i], []);
                    (itep1i, Itep1AST, [Not lhs; Not c; y], [], []);
                    (iten2i, Iten2AST, [rhs; Not x; Not y], [], []);
                    (resi2, ResoAST, [Not lhs; Not c; rhs], [itep1i; iten2i], []);
                    (generate_id (), ResoAST, [rhs], [resi1; resi2; a2bi], [])] in
         (*
             RTL:
             ------------------itep1  -------------------iten2  -------------------itep2  ------------------iten1
             ~(ite c y x), c, x       ite ~c x y, ~~c, ~x       ~(ite c y x), ~c, y       ite ~c x y, ~c, ~y
             --------------------------------------------res    --------------------------------------------res  ---------asmp
                    ~(ite c y x), c, ite ~c x y                       ~(ite c y x), ~c, ite ~c x y               ite c y x
                    -------------------------------------------------------------------------------------------------------res  
                                                                 ite ~c x y     
         *)
         let b2ai = generate_id () in
         let itep1i = generate_id () in
         let iten2i = generate_id () in
         let resi1 = generate_id () in
         let itep2i = generate_id () in
         let iten1i = generate_id () in
         let resi2 = generate_id () in
         let b2a = [(itep1i, Itep1AST, [Not rhs; c; x], [], []);
                    (iten2i, Iten2AST, [lhs; c; Not x], [], []);
                    (resi1, ResoAST, [Not rhs; c; lhs], [itep1i; iten2i], []);
                    (itep2i, Itep2AST, [Not rhs; Not c; y], [], []);
                    (iten1i, Iten1AST, [lhs; Not c; Not y], [], []);
                    (resi2, ResoAST, [Not rhs; Not c; lhs], [itep2i; iten1i], []);
                    (generate_id (), ResoAST, [lhs], [resi1; resi2; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c (ite c x y) z <-> ite c x z *)
       | [Eq ((Ite [c; (Ite [c'; x; y] as lhs'); z] as lhs), (Ite [c''; x'; z'] as rhs))] when c = c' && c = c'' && x = x' && z = z' ->
         (*
             LTR:
            -------------------------------------itep2  --------------------itep2  -----------------iten2  ----------------------------itep1  ----------------iten1
            ~(ite c (ite c x y) z), ~c, ite c x y        ~(ite c x y), ~c, x       ite c x z, ~c, ~x       ~(ite c (ite c x y) z), c, z       ite c x z, c, ~z
            ----------------------------------------------------------------------------------------res    ---------------------------------------------------res  -------------------asmp
                                     ~(ite c (ite c x y) z), ~c, ite c x z                                        ~(ite c (ite c x y) z), c, ite c x z             ite c (ite c x y) z
                                     -------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                                    ite c x z
         *)
         let a2bi = generate_id () in
         let itep2i1 = generate_id () in
         let itep2i2 = generate_id () in
         let iten2i = generate_id () in
         let resi1 = generate_id () in
         let itep1i = generate_id () in
         let iten1i = generate_id () in
         let resi2 = generate_id () in
         let a2b = [(itep2i1, Itep2AST, [Not lhs; Not c; lhs'], [], []);
                    (itep2i2, Itep2AST, [Not lhs'; Not c; x], [], []);
                    (iten2i, Iten2AST, [rhs; Not c; Not x], [], []);
                    (resi1, ResoAST, [Not lhs; Not c; rhs], [itep2i1; itep2i2; iten2i], []);
                    (itep1i, Itep1AST, [Not lhs; c; z], [], []);
                    (iten1i, Iten1AST, [rhs; c; Not z], [], []);
                    (resi2, ResoAST, [Not lhs; c; rhs], [itep1i; iten1i], []);
                    (generate_id (), ResoAST, [rhs], [resi1; resi2; a2bi], [])] in
         (*
             RTL:
             -------------------itep2  ------------------iten2 -------------------------------------iten2  --------------------------iten1  ------------------itep1
             ~(ite c x z), ~c, x       ite c x y, ~c, ~x       ite c (ite c x y) z, ~c, ~(ite c x y)       ite c (ite c x y) z, c, ~z       ~(ite c x z), c, z
             ---------------------------------------------------------------------------------------res     ---------------------------------------------------res  ---------asmp
                                    ~(ite c x z), ~c, ite c (ite c x y) z                                           ite c (ite c x y) z, c, ~(ite c x z)            ite c x z
                                    -----------------------------------------------------------------------------------------------------------------------------------------res
                                                                                              ite c (ite c x y) z
         *)
         let b2ai = generate_id () in
         let itep2i = generate_id () in
         let iten2i1 = generate_id () in
         let iten2i2 = generate_id () in
         let resi1 = generate_id () in
         let iten1i = generate_id () in
         let itep1i = generate_id () in
         let resi2 = generate_id () in
         let b2a = [(itep2i, Itep2AST, [Not rhs; Not c; x], [], []);
                    (iten2i1, Iten2AST, [lhs'; Not c; Not x], [], []);
                    (iten2i2, Iten2AST, [lhs; Not c; Not lhs'], [], []);
                    (resi1, ResoAST, [Not rhs; Not c; lhs], [itep2i; iten2i1; iten2i2], []);
                    (iten1i, Iten1AST, [lhs; c; Not z], [], []);
                    (itep1i, Itep1AST, [Not rhs; c; z], [], []);
                    (resi2, ResoAST, [lhs; c; Not rhs], [iten1i; itep1i], []);
                    (generate_id (), ResoAST, [rhs], [resi1; resi2; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c x (ite c y z) <-> ite c x z *)
       | [Eq ((Ite [c; x; (Ite [c'; y; z] as lhs')] as lhs), (Ite [c''; x'; z'] as rhs))] when c = c' && c = c'' && x = x' && z = z' ->
         (*
             LTR:
             ------------------------------------itep1  ------------------itep1  ----------------iten1  -----------------------------itep2  -----------------iten2
             ~(ite c x (ite c y z)), c, ite c y z       ~(ite c y z), c, z       ite c x z, c, ~z       ~(ite c x (ite c y z)), ~c, x       ite c x z, ~c, ~x
             ------------------------------------------------------------------------------------res    -----------------------------------------------------res   -------------------asmp
                                            ~(ite c x (ite c y z)), c, ite c x z                              ~(ite c x (ite c y z)), ~c, ite c x z                ite c x (ite c y z)
                                            ------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                                               ite c x z
         *)
         let a2bi = generate_id () in
         let itep1i1 = generate_id () in
         let itep1i2 = generate_id () in
         let iten1i = generate_id () in
         let resi1 = generate_id () in
         let itep2i = generate_id () in
         let iten2i = generate_id () in
         let resi2 = generate_id () in
         let a2b = [(itep1i1, Itep1AST, [Not lhs; c; lhs'], [], []);
                    (itep1i2, Itep1AST, [Not lhs'; c; z], [], []);
                    (iten1i, Iten1AST, [rhs; c; Not z], [], []);
                    (resi1, ResoAST, [Not lhs; c; rhs], [itep1i1; itep1i2; iten1i], []);
                    (itep2i, Itep2AST, [Not lhs; Not c; x], [], []);
                    (iten2i, Iten2AST, [rhs; Not c; Not x], [], []);
                    (resi2, ResoAST, [Not lhs; Not c; rhs], [itep2i; iten2i], []);
                    (generate_id (), ResoAST, [rhs], [resi1; resi2; a2bi], [])] in
         (* 
             RTL:
             -------------------itep1  ----------------iten1  ------------------------------------iten1  ---------------------------iten2  -------------------itep2
             ~(ite c x z), c, z        ite c y z, c, ~z       ite c x (ite c y z), c, ~(ite c y z)       ite c x (ite c y z), ~c, ~x       ~(ite c x z), ~c, x
             -------------------------------------------------------------------------------------res    -----------------------------------------------------res  ---------asmp
                                      ~(ite c x z), c, ite c x (ite c y z)                                     ite c x (ite c y z), ~c, ~(ite c x z)               ite c x z
                                      --------------------------------------------------------------------------------------------------------------------------------------res
                                                                                             ite c x (ite c y z)
         *)
         let b2ai = generate_id () in
         let itep1i = generate_id () in
         let iten1i1 = generate_id () in
         let iten1i2 = generate_id () in
         let resi1 = generate_id () in
         let iten2i = generate_id () in
         let itep2i = generate_id () in
         let resi2 = generate_id () in
         let b2a = [(itep1i, Itep1AST, [Not rhs; c; z], [], []);
                    (iten1i1, Iten1AST, [lhs'; c; Not z], [], []);
                    (iten1i2, Iten1AST, [lhs; c; Not lhs'], [], []);
                    (resi1, ResoAST, [Not rhs; c; lhs], [itep1i; iten1i1; iten1i2], []);
                    (iten2i, Iten2AST, [lhs; Not c; Not x], [], []);
                    (itep2i, Itep2AST, [Not rhs; Not c; x], [], []);
                    (resi2, ResoAST, [lhs; Not c; Not rhs], [iten2i; itep2i], []);
                    (generate_id (), ResoAST, [lhs], [resi1; resi2; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c T F <-> c *)
       | [Eq ((Ite [c; True; False] as lhs), (c' as rhs))] when c = c' ->
         (*
             LTR:
             ------------------itep1  ---F  ----------asmp
             ~(ite c T F), c, F       ~F    ite c T F
             ----------------------------------------res
                                 c
         *)
         let a2bi = generate_id () in
         let itep1i = generate_id () in
         let fi = generate_id () in
         let a2b = [(itep1i, Itep1AST, [Not lhs; c; False], [], []);
                    (fi, FalsAST, [Not False], [], []);
                    (generate_id (), ResoAST, [rhs], [itep1i; fi; a2bi], [])] in
         (*
             RTL:
             -----------------iten2  ---T  ---asmp
             ite c T F, ~c, ~T        T     c
             --------------------------------res
                        ite c T F
         *)
         let b2ai = generate_id () in
         let iten2i = generate_id () in
         let ti = generate_id () in
         let b2a = [(iten2i, Iten2AST, [lhs; Not c; Not True], [], []);
                    (ti, TrueAST, [True], [], []);
                    (generate_id (), ResoAST, [lhs], [iten2i; ti; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c F T <-> ~c *)
       | [Eq ((Ite [c; False; True] as lhs), (Not c' as rhs))] when c = c' ->
         (*
             LTR:
             --------------------itep2  ---F  ----------asmp
             ~(ite c F T), ~c, F         ~F   ite c F T
             -------------------------------------------res
                                ~c
         *)
         let a2bi = generate_id () in
         let itep2i = generate_id () in
         let fi = generate_id () in
         let a2b = [(itep2i, Itep2AST, [Not lhs; Not c; False], [], []);
                    (fi, FalsAST, [Not False], [], []);
                    (generate_id (), ResoAST, [rhs], [itep2i; fi; a2bi], [])] in
         (*
             RTL:
             ----------------iten1  ---T  ---asmp
             ite c F T, c, ~T        T    ~c
             -------------------------------res
                       ite c F T
         *)
         let b2ai = generate_id () in
         let iten1i = generate_id () in
         let ti = generate_id () in
         let b2a = [(iten1i, Iten1AST, [lhs; c; Not True], [], []);
                    (ti, TrueAST, [True], [], []);
                    (generate_id (), ResoAST, [lhs], [iten1i; ti; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c T x <-> c v x *)
       | [Eq ((Ite [c; True; x] as lhs), (Or [c'; x'] as rhs))] when c = c' && x = x' ->
         (*
             LTR:
             ------------------itep1  ---------orn  ---------orn ---------asmp
             ~(ite c T x), c, x       c v x, ~c     c v x, ~x    ite c T x    
             ---------------------------------------------------------------res
                                        c v x
         *)
         let a2bi = generate_id () in
         let itep1i = generate_id () in
         let orni1 = generate_id () in
         let orni2 = generate_id () in
         let a2b = [(itep1i, Itep1AST, [Not lhs; c; x], [], []);
                    (orni1, OrnAST, [rhs; Not c], [], ["1"]);
                    (orni2, OrnAST, [rhs; Not x], [], ["2"]);
                    (generate_id (), ResoAST, [rhs], [itep1i; orni1; orni2; a2bi], [])] in
         (*
             RTL:
             --------------orp  -----------------iten1  -----------------iten2  ---T  -----asmp
             ~(c v x), c, x     ite c T x, c, ~x        ite c T x, ~c, ~T        T    c v x
             ------------------------------------------------------------------------------res
                                              ite c T x
             
         *)
         let b2ai = generate_id () in
         let orpi = generate_id () in
         let iten1i = generate_id () in
         let iten2i = generate_id () in
         let ti = generate_id () in
         let b2a = [(orpi, OrpAST, [Not rhs; c; x], [], []);
                    (iten1i, Iten1AST, [lhs; c; Not x], [], []);
                    (iten2i, Iten2AST, [lhs; Not c; Not True], [], []);
                    (ti, TrueAST, [True], [], []);
                    (generate_id (), ResoAST, [lhs], [orpi; iten1i; iten2i; ti; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c x F <-> c ^ x *)
       | [Eq ((Ite [c; x; False] as lhs), (And [c'; x'] as rhs))] when c = c' && x = x' ->
         (*
             LTR:
             ---------------andn  -------------------itep2  ------------------itep1  ---F  ---------asmp
             c ^ x, ~c, ~x        ~(ite c x F), ~c, x       ~(ite c x F), c, F        ~F    ite c x F
             -------------------------------------------------------------------------------------res
                                                    c ^ x
         *)
         let a2bi = generate_id () in
         let andni = generate_id () in
         let itep2i = generate_id () in
         let itep1i = generate_id () in
         let fi = generate_id () in
         let a2b = [(andni, AndnAST, [rhs; Not c; Not x], [], []);
                    (itep2i, Itep2AST, [Not lhs; Not c; x], [], []);
                    (itep1i, Itep1AST, [Not lhs; c; False], [], []);
                    (fi, FalsAST, [Not False], [], []);
                    (generate_id (), ResoAST, [rhs], [andni; itep2i; itep1i; fi; a2bi], [])] in
         (*
             RTL:
             -----------------iten2  -----------andp  -----------andp  -----asmp
             ite c x F, ~c, ~x       ~(c ^ x), c      ~(c ^ x), x      c ^ x
             ---------------------------------------------------------------res
                                       ite c x F
            
            ------------------iten1 -----------andp
            ite c x F, ~c , ~x      ~(c ^ x), c
            ------------------------------------res -----------andp
                  ite c x F, ~x, ~(c ^ x)           ~(c ^ x), x
                  ---------------------------------------------res  -----asmp
                              ite c x F, ~(c ^ x)                   c ^ x
                              -------------------------------------------res
                                                ite c x F
         *)
         let b2ai = generate_id () in
         let iten1i = generate_id () in
         let andpi1 = generate_id () in
         let andpi2 = generate_id () in
         let resi1 = generate_id () in
         let resi2 = generate_id () in
         let b2a = [(iten1i, Iten2AST, [lhs; Not c; Not x], [], []);
                    (andpi1, AndpAST, [Not rhs; c], [], ["0"]);
                    (resi1, ResoAST, [lhs; Not rhs; Not x], [iten1i; andpi1], []);
                    (andpi2, AndpAST, [Not rhs; x], [], ["1"]);
                    (resi2, ResoAST, [lhs; Not rhs], [resi1; andpi2], []);
                    (generate_id (), ResoAST, [lhs], [resi2; b2ai], [])] in
                    (*(generate_id (), ResoAST, [lhs], [iten1i; andpi1; andpi2; b2ai], [])] in*)
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c F x <-> ~c ^ x *)
       | [Eq ((Ite [c; False; x] as lhs), (And [Not c'; x'] as rhs))] when c = c' && x = x' ->
         (*
             LTR:
             ---------------andn ------------------itep1  -------------------itep2  ---F  ---------asmp
             ~c ^ x, ~~c, ~x     ~(ite c F x), c, x       ~(ite c F x), ~c, F        ~F   ite c F x
             --------------------------------------------------------------------------------------res
                                                  ~c ^ x
         *)
         let a2bi = generate_id () in
         let andni = generate_id () in
         let itep1i = generate_id () in
         let itep2i = generate_id () in
         let fi = generate_id () in
         let a2b = [(andni, AndnAST, [rhs; c; Not x], [], []);
                    (itep1i, Itep1AST, [Not lhs; c; x], [], []);
                    (itep2i, Itep2AST, [Not lhs; Not c; False], [], []);
                    (fi, FalsAST, [Not False], [], []);
                    (generate_id (), ResoAST, [rhs], [andni; itep1i; itep2i; fi; a2bi], [])] in
         (*
             RTL:
             ----------------iten1  -------------andp  --------------andp  ------asmp
             ite c F x, c, ~x       ~(~c ^ x), ~c        ~(~c ^ x), x      ~c ^ x
            ---------------------------------------------------------------------res
                                          ite c F x
         *)
         let b2ai = generate_id () in
         let iten1i = generate_id () in
         let andpi1 = generate_id () in
         let andpi2 = generate_id () in
         let b2a = [(iten1i, Iten1AST, [lhs; c; Not x], [], []);
                    (andpi1, AndpAST, [rhs; Not c], [], ["0"]);
                    (andpi2, AndpAST, [rhs; x], [], ["1"]);
                    (generate_id (), ResoAST, [lhs], [iten1i; andpi1; andpi2; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c x T <-> ~c v x *)
       | [Eq ((Ite [c; x; True] as lhs), (Or [Not c'; x'] as rhs))] when c = c' && x = x' ->
         (*
             LTR:
             -------------------itep2  -----------orn  ----------orn  ---------asmp
             ~(ite c x T), ~c, x       ~c v x, ~~c     ~c v x, ~x     ite c x T
             ------------------------------------------------------------------res
                                          ~c v x
         *)
         let a2bi = generate_id () in
         let itep2i = generate_id () in
         let orni1 = generate_id () in
         let orni2 = generate_id () in
         let a2b = [(itep2i, Itep2AST, [Not lhs; Not c; x], [], []);
                    (orni1, OrnAST, [rhs; c], [], ["0"]);
                    (orni2, OrnAST, [rhs; Not x], [], ["1"]);
                    (generate_id (), ResoAST, [rhs], [itep2i; orni1; orni2; a2bi], [])] in
         (*
             ----------------orp ------asmp  -----------------iten2  -----------------iten1  ---true
             ~(~c v x), ~c, x    ~c v x      ite c x T, ~c, ~x       ite c x T, c, ~T         T
             ----------------------------------------------------------------------------------res    
                                                   ite c x T
         *)
         let b2ai = generate_id () in
         let orpi = generate_id () in
         let iten2i = generate_id () in
         let iten1i = generate_id () in
         let ti = generate_id () in
         let b2a = [(orpi, OrpAST, [Not rhs; Not c; x], [], []);
                    (iten2i, Iten2AST, [lhs; Not c; Not x], [], []);
                    (iten1i, Iten1AST, [lhs; c; Not True], [], []);
                    (ti, TrueAST, [True], [], []);
                    (generate_id (), ResoAST, [lhs], [orpi; b2ai; iten2i; iten1i; ti], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
      | [Eq _] -> raise (Debug ("| process_simplify: unexpected form of equivalence for ite_simplify at id "^i^" |"))
      | _ -> raise (Debug ("| process_simplify: expecting ite_simplify to derive a singleton equivalence at id "^i^" |")))
  (* x <-> y *)
  | (i, BoolsimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
       (* ~(x -> y) <-> (x ^ ~y) *)
       | [Eq ((Not (Imp [x; y]) as lhs), (And [a; Not b] as rhs))] when (x = a && y = b) ->
         (*
             LTR:
                                 ---------asmp  -----------impn1  ---------asmp   ------------impn2
                                 ~(x -> y)      (x -> y), x       ~(x -> y)       (x -> y), ~y
             ---------------andn --------------------------res    ----------------------------res     
             x ^ ~y, ~x, ~~y                  x                                ~y
             --------------------------------------------------------------------res
                                             x ^ ~y
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
         (*
             RTL:
                                    -------asmp  ------------andp      ------asmp    -------------andp
                                    x ^ ~y       ~(x ^ ~y), x          x ^ ~y        ~(x ^ ~y), ~y
             ----------------impp   -------------------------res       ---------------------------res    
             ~(x -> y), ~x, y                   x                                   ~y                   
             -------------------------------------------------------------------------res
                                             ~(x -> y)
         *)
         let b2ai = generate_id () in
         let andp_1i = generate_id () in
         let res_3i = generate_id () in
         let andp_2i = generate_id () in
         let res_4i = generate_id () in
         let imppi = generate_id () in
         let b2a = [(andp_1i, AndpAST, [Not rhs; x], [], ["0"]);
                    (res_3i, ResoAST, [x], [andp_1i;b2ai], []);
                    (andp_2i, AndpAST, [Not rhs; Not y], [], ["1"]);
                    (res_4i, ResoAST, [Not y], [andp_2i;b2ai], []);
                    (imppi, ImppAST, [lhs; Not x; y], [], []);
                    (generate_id (), ResoAST, [lhs], [imppi;res_3i;res_4i], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ~(x v y) <-> (~x ^ ~y) *)
       | [Eq ((Not (Or [x;y]) as lhs), (And [Not a;Not b] as rhs))] when (x = a && y = b) ->
         (*
            LTR:
                                    --------asmp  ---------orn      --------asmp  ---------orn
                                    ~(x v y)      x v y, ~x         ~(x v y)      x v y, ~y
            -----------------andn   -----------------------res      -----------------------res    
            ~x ^ ~y, ~~x, ~~y                 ~x                               ~y
            ---------------------------------------------------------------------res
                                             ~x ^ ~y
         *)
         let a2bi = generate_id () in
         let orn_1i = generate_id () in
         let res_1i = generate_id () in
         let orn_2i = generate_id () in
         let res_2i = generate_id () in
         let andni = generate_id () in
         let a2b = [(orn_1i, OrnAST, [Or [x;y]; Not x], [], ["0"]);
                    (res_1i, ResoAST, [Not x], [orn_1i;a2bi], []);
                    (orn_2i, OrnAST, [Or [x;y]; Not y], [], ["1"]);
                    (res_2i, ResoAST, [Not y], [orn_2i;a2bi], []);
                    (andni, AndnAST, [rhs; Not x; Not y], [], []);
                    (generate_id (), ResoAST, [rhs], [andni;res_1i;res_2i], [])] in
         (*
            RTL:
                              -------asmp   --------------andp      -------asmp   --------------andp
                              ~x ^ ~y       ~(~x ^ ~y), ~x          ~x ^ ~y       ~(~x ^ ~y), ~y
            --------------orp ----------------------------res       ------------------------------res
            ~(x v y), x, y                ~x                                      ~y
            ------------------------------------------------------------------------res
                                             ~(x v y)
         *)
         let b2ai = generate_id () in
         let andp_1i = generate_id () in
         let res_3i = generate_id () in
         let andp_2i = generate_id () in
         let res_4i = generate_id () in
         let orpi = generate_id () in
         let b2a = [(andp_1i, AndpAST, [Not rhs; Not x], [], ["0"]);
                    (res_3i, ResoAST, [Not x], [andp_1i;b2ai], []);
                    (andp_2i, AndpAST, [Not rhs; Not y], [], ["1"]);
                    (res_4i, ResoAST, [Not y], [andp_2i;b2ai], []);
                    (orpi, OrpAST, [lhs; x; y], [], []);
                    (generate_id (), ResoAST, [lhs], [orpi;res_3i;res_4i], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ~(x ^ y) <-> (~x v ~y) *)
       | [Eq ((Not (And [x;y]) as lhs), (Or [Not a;Not b] as rhs))] when (x = a && y = b) ->
         (*
            LTR:
            ---------------andn  --------asmp   ------------orn  ------------orn
            (x ^ y), ~x, ~y      ~(x ^ y)       ~x v ~y, ~~x     ~x v ~y, ~~y
            ----------------------------------------------------------------res
                                         ~x v ~y
         *)
         let a2bi = generate_id () in
         let andni = generate_id () in
         let orni1 = generate_id () in
         let orni2 = generate_id () in
         let a2b = [(andni, AndnAST, [And [x;y]; Not x; Not y], [], []);
                    (orni1, OrnAST, [rhs; x], [], ["0"]);
                    (orni2, OrnAST, [rhs; y], [], ["1"]);
                    (generate_id (), ResoAST, [rhs], [andni; a2bi; orni1; orni2], [])] in
         (*
            RTL:
            ------------------orp   -------asmp -----------andp   -----------andp
            ~(~x v ~y), ~x, ~y      ~x v ~y     ~(x ^ y), x       ~(x ^ y), y
            -----------------------------------------------------------------res
                                         ~(x ^ y)
         *)
         let b2ai = generate_id () in
         let orpi = generate_id () in
         let andpi1 = generate_id () in
         let andpi2 = generate_id () in
         let b2a = [(orpi, OrpAST, [Not rhs; Not x; Not y], [], []);
                    (andpi1, AndpAST, [lhs; x], [], ["0"]);
                    (andpi2, AndpAST, [lhs; y], [], ["1"]);
                    (generate_id (), ResoAST, [lhs], [orpi; b2ai; andpi1; andpi2], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x -> (y -> z)) <-> ((x ^ y) -> z) *)
       | [Eq ((Imp [x; Imp [y; z]] as lhs), (Imp [And [a; b]; c] as rhs))] when x = a && y = b && z = c ->
         (*
            LTR:
            ----------------------------impp -------------asmp   ---------------impp  -----------andp -----------andp  ----------------impn2   -------------------impn1
            ~(x -> (y -> z)), ~x, y -> z     x -> (y -> z)       ~(y -> z), ~y, z     ~(x ^ y), x     ~(x ^ y), y      (x ^ y) -> z, ~z        (x ^ y) -> z, x ^ y     
            -------------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                       (x ^ y) -> z
                                                                             
         *)
         let a2bi = generate_id () in
         let imppi1 = generate_id () in
         let imppi2 = generate_id () in
         let andpi1 = generate_id () in
         let andpi2 = generate_id () in
         let impn2i1 = generate_id () in
         let impn1i1 = generate_id () in
         let a2b = [(imppi1, ImppAST, [Not lhs; Not x; Imp [y; z]], [], []);
                    (imppi2, ImppAST, [Not (Imp [y; z]); Not y; z], [], []);
                    (andpi1, AndpAST, [Not (And [x; y]); x], [], ["0"]);
                    (andpi2, AndpAST, [Not (And [x; y]); y], [], ["1"]);
                    (impn2i1, Impn2AST, [Imp [And [x; y]; z]; Not z], [], []);
                    (impn1i1, Impn1AST, [Imp [And [x; y]; z]; And [x; y]], [], []);
                    (generate_id (), ResoAST, [rhs], [imppi1; a2bi; imppi2; andpi1; andpi2; impn2i1; impn1i1], [])] in
         (*
            RTL:
            --------------------------impp  ----------asmp  ---------------andn  ----------impn2   ------------------impn1 ----------impn1   ------------------------impn2
            ~(x ^ y -> z), ~(x ^ y), z      x ^ y -> z      (x ^ y), ~x, ~y      y -> z, ~z         x -> (y -> z), x        y -> z, y        x -> (y -> z), ~(y -> z)
            ---------------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                    x -> (y -> z)
         *)
         let b2ai = generate_id () in
         let imppi3 = generate_id () in
         let andni = generate_id () in
         let impn1i2 = generate_id () in
         let impn1i3 = generate_id () in
         let impn2i2 = generate_id () in
         let impn2i3 = generate_id () in
         let b2a = [(imppi3, ImppAST, [Not rhs; Not (And [x; y]); z], [], []);
                    (andni, AndnAST, [And [x; y]; Not x; Not y], [], []);
                    (impn2i2, Impn2AST, [Imp [y; z]; Not z], [], []);
                    (impn1i2, Impn1AST, [lhs; x], [], []);
                    (impn1i3, Impn1AST, [Imp [y; z]; y], [], []);
                    (impn2i3, Impn2AST, [lhs; Not (Imp [y; z])], [], []);
                    (generate_id (), ResoAST, [lhs], [imppi3; b2ai; andni; impn2i2; impn1i2; impn1i3; impn2i3], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ((x -> y) -> y) <-> (x v y) *)
       | [Eq ((Imp [Imp [x;y]; n] as lhs), (Or [a;b]as rhs))] when y = n && x = a && y = b ->
         (*
            LTR:
            -------------asmp   ------------------------------impp   ---------impn1 ---------orn   ---------orn
            (x -> y) -> y       ~((x -> y) -> y), ~(x -> y), y       x -> y, x      x v y, ~x      x v y, ~y
            ------------------------------------------------------------------------------------------------res
                                                        x v y
         *)
         let a2bi = generate_id () in
         let imppi1 = generate_id () in
         let impni1 = generate_id () in
         let orni1 = generate_id () in
         let orni2 = generate_id () in
         let a2b = [(imppi1, ImppAST, [Not lhs; Not (Imp [x;y]); y], [], []);
                    (impni1, Impn1AST, [Imp [x;y]; x], [], []);
                    (orni1, OrnAST, [rhs; Not x], [], ["0"]);
                    (orni2, OrnAST, [rhs; Not y], [], ["1"]);
                    (generate_id (), ResoAST, [rhs], [a2bi; imppi1; impni1; orni1; orni2], [])] in
         (*
            RTL:
            -----asmp  ---------------orp ----------------impp ---------------impn2 ---------------------impn1
            x v y      ~(x v y), x, y      ~(x -> y), ~x, y    (x -> y) -> y, ~y    (x -> y) -> y, x -> y
            ---------------------------------------------------------------------------------------------res
                                                      (x -> y) -> y
         *)
         let b2ai = generate_id () in
         let orpi = generate_id () in
         let imppi2 = generate_id () in
         let impni2 = generate_id () in
         let impni3 = generate_id () in
         let b2a = [(orpi, OrpAST, [Not rhs; x; y], [], []);
                    (imppi2, ImppAST, [Not (Imp [x;y]); Not x; y], [], []);
                    (impni2, Impn2AST, [lhs; Not y], [], []);
                    (impni3, Impn1AST, [lhs; Imp [x;y]], [], []);
                    (generate_id (), ResoAST, [lhs], [b2ai; orpi; imppi2; impni2; impni3], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* (x ^ (x -> y)) <-> (x ^ y) *)
       | [Eq ((And [x; Imp [m; y]] as lhs), (And [a;b] as rhs))] when x = m && x = a && y = b ->
         (*
            LTR:
            -----------------------andp  ----------------impp  -------------andn ------------------andp  ------------asmp
            ~(x ^ (x -> y)), x -> y      ~(x -> y), ~x, y      x ^ y, ~x, ~y     ~(x ^ (x -> y)), x      x ^ (x -> y)
            ----------------------------------------------------------------------------------------------------------res
                                                               x ^ y
         *)
         let a2bi = generate_id () in
         let andpi1 = generate_id () in
         let imppi = generate_id () in
         let andni = generate_id () in
         let andpi2 = generate_id () in
         let a2b = [(andpi1, AndpAST, [Not lhs; Imp [x; y]], [], ["1"]);
                    (imppi, ImppAST, [Not (Imp [x; y]); Not x; y], [], []);
                    (andni, AndnAST, [rhs; Not x; Not y], [], []);
                    (andpi2, AndpAST, [Not lhs; x], [], ["0"]);
                    (generate_id (), ResoAST, [rhs], [andpi1; imppi; andni; andpi2; a2bi], [])] in
         (*
            RTL:
            ---------------------------andn  ----------impn2   -----------andp  -----------andp -----asmp
            x ^ (x -> y), ~x, ~(x -> y)      x -> y, ~y        ~(x ^ y), x      ~(x ^ y), y     x ^ y
            -----------------------------------------------------------------------------------------res  
                                                  x ^ (x -> y)                                                               
         *)
         let b2ai = generate_id () in
         let impni = generate_id () in
         let andni = generate_id () in
         let andpi1 = generate_id () in
         let andpi2 = generate_id () in
         let b2a = [(andni, AndnAST, [lhs; Not x; Not (Imp [x;y])], [], []);
                    (impni, Impn2AST, [Imp [x; y]; Not y], [], []);
                    (andpi1, AndpAST, [Not rhs; x], [], ["0"]);
                    (andpi2, AndpAST, [Not rhs; y], [], ["1"]);
                    (generate_id (), ResoAST, [lhs], [impni; andni; andpi1; andpi2; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ((x -> y) ^ x) <-> (x ^ y) *)
       | [Eq ((And [Imp [m; y]; x] as lhs), (And [a;b] as rhs))] when x = m && x = a && y = b ->
         (*
            LTR:
            -----------------------andp  ----------------impp  -------------andn ------------------andp  ------------asmp
            ~((x -> y) ^ x), x -> y      ~(x -> y), ~x, y      x ^ y, ~x, ~y     ~((x -> y) ^ x), x      (x -> y) ^ x
            ----------------------------------------------------------------------------------------------------------res
                                                              x ^ y
         *)
         let a2bi = generate_id () in
         let andpi1 = generate_id () in
         let imppi = generate_id () in
         let andni = generate_id () in
         let andpi2 = generate_id () in
         let a2b = [(andpi1, AndpAST, [Not lhs; Imp [x;y]], [], ["0"]);
                    (imppi, ImppAST, [Not (Imp [x;y]); Not x; y], [], []);
                    (andni, AndnAST, [rhs; Not x; Not y], [], []);
                    (andpi2, AndpAST, [Not lhs; x], [], ["1"]);
                    (generate_id (), ResoAST, [rhs], [andpi1; imppi; andni; andpi2; a2bi], [])] in
         (*
            RTL:
            ---------------------------andn  ----------impn2   -----------andp  -----------andp -----asmp
            (x -> y) ^ x, ~(x -> y), ~x      x -> y, ~y        ~(x ^ y), x      ~(x ^ y), y     x ^ y
            -----------------------------------------------------------------------------------------res
                                                     (x -> y) ^ x
         *)
         let b2ai = generate_id () in
         let impni = generate_id () in
         let andni = generate_id () in
         let andpi1 = generate_id () in
         let andpi2 = generate_id () in
         let b2a = [(impni, Impn2AST, [Imp [x; y]; Not y], [], []);
                    (andni, AndnAST, [lhs; Not (Imp [x;y]); Not x], [], []);
                    (andpi1, AndpAST, [Not rhs; x], [], ["0"]);
                    (andpi2, AndpAST, [Not rhs; y], [], ["1"]);
                    (generate_id (), ResoAST, [lhs], [impni; andni; andpi1; andpi2; b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
      | [Eq _] -> raise (Debug ("| process_simplify: unexpected form of equivalence for bool_simplify at id "^i^" |"))
      | _ -> raise (Debug ("| process_simplify: expecting bool_simplify to derive a singleton equivalence at id "^i^" |")))
  | (i, ConndefAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
       (* x xor y <-> (~x ^ y) v (x ^ ~y) *)
       | [Eq ((Xor [x; y] as lhs), (Or [And [Not a; b]; And [c; Not d]] as rhs))] when x = a && x = c && y = b && y = d ->
       (*
           LTR:
           -----------------------------orn  ---------------andn  ----------------xorp1   ------------------------------orn  ---------------andn  ------------------xorp2   
           (~x ^ y) v (x ^ ~y), ~(x ^ ~y)    x ^ ~y, ~x, ~~y       ~(x xor y), x, y       (~x ^ y) v (x ^ ~y), ~(~x ^ y)     ~x ^ y, ~~x, ~y      ~(x xor y), ~x, ~y          
           ------------------------------------------------------------------------res    --------------------------------------------------------------------------res    -------asmp
                               (~x ^ y) v (x ^ y), ~(x xor y), y                                           (~x ^ y) v (x ^ ~y), ~(x xor y), ~y                             x xor y
                            ------------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                          (~x ^ y) v (x ^ ~y)
       *)
       let a2bi = generate_id () in
       let orni1 = generate_id () in
       let andni1 = generate_id () in
       let xorp1i = generate_id () in
       let resi1 = generate_id () in
       let orni2 = generate_id () in
       let andni2 = generate_id () in
       let xorp2i = generate_id () in
       let resi2 = generate_id () in
       let a2b = [(orni1, OrnAST, [rhs; Not (And [x; Not y])], [], ["1"]);
                  (andni1, AndnAST, [And [x; Not y]; Not x; y], [], []);
                  (xorp1i, Xorp1AST, [Not lhs; x; y], [], []);
                  (resi1, ResoAST, [rhs; Not lhs; y], [orni1; andni1; xorp1i], []);
                  (orni2, OrnAST, [rhs; Not (And [Not x; y])], [], ["0"]);
                  (andni2, AndnAST, [And [Not x; y]; x; Not y], [], []);
                  (xorp2i, Xorp2AST, [Not lhs; Not x; Not y], [], []);
                  (resi2, ResoAST, [rhs; Not lhs; Not y], [orni2; andni2; xorp2i], []);
                  (generate_id (), ResoAST, [rhs], [resi1; resi2; a2bi], [])] in
       (*     
           RTL:
                                                                                 --------------xorn1  -------------andp  ------------andp  --------------xorn2  -------------andp  -------------andp
                                                                                 x xor y, x, ~y       ~(~x ^ y), ~x      ~(~x ^ y), y      x xor y, ~x, y       ~(x ^ ~y), x        ~(x ^ ~y), ~y
           -------------------asmp  ---------------------------------------orp  ----------------------------------------------------res   ------------------------------------------------------res
           (~x ^ y) v (x ^ ~y)      ~((~x ^ y) v (x ^ ~y)), ~x ^ y, x ^ ~y                       x xor y, ~(~x ^ y)                                        x xor y, ~(x ^ ~y)
           ------------------------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                         x xor y
       *)
       let b2ai = generate_id () in
       let andpi1 = generate_id () in
       let xorn1i = generate_id () in
       let andpi2 = generate_id () in
       let resi1 = generate_id () in
       let andpi3 = generate_id () in
       let xorn2i = generate_id () in
       let andpi4 = generate_id () in
       let resi2 = generate_id () in
       let orpi = generate_id () in
       let b2a = [(orpi, OrpAST, [Not rhs; And [Not x; y]; And [x; Not y]], [], []);
                  (xorn1i, Xorn1AST, [lhs; x; Not y], [], []);           
                  (andpi1, AndpAST, [Not (And [Not x; y]); Not x], [], ["0"]);
                  (andpi2, AndpAST, [Not (And [Not x; y]); y], [], ["1"]);
                  (resi1, ResoAST, [lhs; Not (And [Not x; y])], [xorn1i; andpi1; andpi2], []);
                  (xorn2i, Xorn2AST, [lhs; Not x; y], [], []);
                  (andpi3, AndpAST, [Not (And [x; Not y]); x], [], ["0"]);
                  (andpi4, AndpAST, [Not (And [x; Not y]); Not y], [], ["1"]);
                  (resi2, ResoAST, [lhs; Not (And [x; Not y])], [xorn2i; andpi3; andpi4], []);
                  (generate_id (), ResoAST, [lhs], [b2ai; orpi; resi1; resi2], [])] in
       (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* x <-> y <-> (x -> y) ^ (y -> x) *)
       | [Eq ((Eq (x, y) as lhs), (And [Imp [a;b]; Imp [d;c]] as rhs))] when x = a && x = c && y = b && y = d ->
       (*
           LTR:
                                                             ------------------eqp1  ---------impn1  ----------impn2  ------------------eqp2  ---------impn1  ----------impn2
                                                             ~(x <-> y), x , ~y      y -> x, y       y -> x, ~x       ~(x <-> y), ~x , y      x -> y, x       x -> y, ~y
           -----------------------------------------andn     --------------------------------------------------res    --------------------------------------------------res  -------asmp          
           (x -> y) ^ (y -> x), ~(x -> y), ~(y -> x)                        ~(x <-> y), y -> x                                       ~(x <-> y), x -> y                      x <-> y
           -------------------------------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                    (x -> y) ^ (y -> x)
       *)
       let a2bi = generate_id () in
       let eqp1i = generate_id () in
       let impn1i1 = generate_id () in
       let impn2i1 = generate_id () in
       let resi1 = generate_id () in
       let eqp2i = generate_id () in
       let impn1i2 = generate_id () in
       let impn2i2 = generate_id () in
       let resi2 = generate_id () in
       let andni = generate_id () in
       let a2b = [(andni, AndnAST, [rhs; Not (Imp [x; y]); Not (Imp [y; x])], [], []);
                  (eqp1i, Equp1AST, [Not lhs; x; Not y], [], []);
                  (impn1i1, Impn1AST, [Imp [y; x]; y], [], []);
                  (impn2i1, Impn2AST, [Imp [y; x]; Not x], [], []);
                  (resi1, ResoAST, [Not lhs; Imp [y; x]], [eqp1i; impn1i1; impn2i1], []);
                  (eqp2i, Equp2AST, [Not lhs; Not x; y], [], []);
                  (impn1i2, Impn1AST, [Imp [x; y]; x], [], []);
                  (impn2i2, Impn2AST, [Imp [x; y]; Not y], [], []);
                  (resi2, ResoAST, [Not lhs; Imp [x; y]], [eqp2i; impn1i2; impn2i2], []);
                  (generate_id (), ResoAST, [rhs], [andni; resi1; resi2; a2bi], [])] in
       (*
           RTL:
           ------------------------------andp  ----------------impp  -------------eqn2  ------------------------------andp  ----------------impp  ----------------eqn1
           ~((x -> y) ^ (y -> x)), x -> y      ~(x -> y), ~x, y      x <-> y, x, y      ~((x -> y) ^ (y -> x)), y -> x      ~(y -> x), ~y, x      x <-> y, ~x, ~y
           -----------------------------------------------------------------------res   -------------------------------------------------------------------------res  -------------------asmp
                              ~((x -> y) ^ (y -> x)), x <-> y, y                                           ~((x -> y) ^ (y -> x)), x <-> y, ~y                        (x -> y) ^ (y -> x)
                              -----------------------------------------------------------------------------------------------------------------------------------------------------------res
                                                                                               x <-> y
       *)
       let b2ai = generate_id () in
       let andpi1 = generate_id () in
       let imppi1 = generate_id () in
       let eqn2i = generate_id () in
       let resi1 = generate_id () in
       let andpi2 = generate_id () in
       let imppi2 = generate_id () in
       let eqn1i = generate_id () in
       let resi2 = generate_id () in
       let b2a = [(andpi1, AndpAST, [Not rhs; Imp [x; y]], [], ["0"]);
                  (imppi1, ImppAST, [Not (Imp [x; y]); Not x; y], [], []);
                  (eqn2i, Equn2AST, [lhs; x; y], [], []);
                  (resi1, ResoAST, [Not rhs; lhs; y], [andpi1; imppi1; eqn2i], []);
                  (andpi2, AndpAST, [Not rhs; Imp [y; x]], [], ["1"]);
                  (imppi2, ImppAST, [Not (Imp [y; x]); Not y; x], [], []);
                  (eqn1i, Equn1AST, [lhs; Not x; Not y], [], []);
                  (resi2, ResoAST, [Not rhs; lhs; Not y], [andpi2; imppi2; eqn1i], []);
                  (generate_id (), ResoAST, [lhs], [resi1; resi2; b2ai], [])] in
       (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ite c x y <-> (c -> x) ^ (~c -> y) *)
       | [Eq ((Ite [c;x;y] as lhs), (And [Imp [c'; a]; Imp [Not c''; b]] as rhs))] when c = c' && c = c'' && x = a && y = b ->
       (*
           LTR:
                                                            ------------------itep1  -----------impn1  -----------impn2  -------------------itep2  ---------impn1  ----------impn2
                                                            ~(ite c x y), c, y       ~c -> y, ~c       ~c -> y, ~y       ~(ite c x y), ~c, x       c -> x, c       c -> x, ~x
           -------------------------------------------andn  ------------------------------------------------------res    ------------------------------------------------------res  ---------asmp
           (c -> x) ^ (~c -> y), ~(c -> x), ~(~c -> y)                  ~(ite c x y), ~c -> y                                        ~(ite c x y), c -> x                           ite c x y
           ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
                                                                                      (c -> x) ^ (~c -> y)
       *)
       let a2bi = generate_id () in
       let itepi1 = generate_id () in
       let impni1 = generate_id () in
       let impni2 = generate_id () in
       let resi1 = generate_id () in
       let itepi2 = generate_id () in
       let impni3 = generate_id () in
       let impni4 = generate_id () in
       let resi2 = generate_id () in 
       let andni = generate_id () in
       let a2b = [(itepi1, Itep1AST, [Not lhs; c; y], [], []);
                  (impni1, Impn1AST, [Imp [Not c; y]; Not c], [], []);
                  (impni2, Impn2AST, [Imp [Not c; y]; Not y], [], []);
                  (resi1, ResoAST, [Not lhs; Imp [Not c; y]], [itepi1; impni1; impni2], []);
                  (itepi2, Itep2AST, [Not lhs; Not c; x], [], []);
                  (impni3, Impn1AST, [Imp [c; x]; c], [], []);
                  (impni4, Impn2AST, [Imp [c; x]; Not x], [], []);
                  (resi2, ResoAST, [Not lhs; Imp [c; x]], [itepi2; impni3; impni4], []);
                  (andni, AndnAST, [rhs; Not (Imp [c; x]); Not (Imp [Not c; y])], [], []);
                  (generate_id (), ResoAST, [rhs], [andni; resi1; resi2; a2bi], [])] in
       (*
           RTL:
           ----------------iten1  ------------------impp  -----------------iten2  ----------------impp
           ite c x y, c, ~y       ~(~c -> y), ~~c, y      ite c x y, ~c, ~x       ~(c -> x), ~c, x
           -----------------------------------------res   -----------------------------------------res
                   ite c x y, c, ~(~c -> y)                       ite c x y, ~c, ~(c -> x)
                   -----------------------------------------------------------------------res  -------------------------------andp  --------------------------------andp  --------------------asmp
                                     ite c x y, ~(~c -> y), ~(c -> x)                          ~((c -> x) ^ (~c -> y)), c -> x      ~((c -> x) ^ (~c -> y)), ~c -> y      (c -> x) ^ (~c -> y)
                                  res---------------------------------------------------------------------------------------------------------------------------------------------------------
                                                                                                        ite c x y
       *)
       let b2ai = generate_id () in
       let iteni1 = generate_id () in
       let imppi1 = generate_id () in
       let resi1 = generate_id () in
       let iteni2 = generate_id () in
       let imppi2 = generate_id () in
       let resi2 = generate_id () in
       let andpi1 = generate_id () in
       let andpi2 = generate_id () in
       let b2a = [(iteni1, Iten1AST, [lhs; c; Not y], [], []);
                  (imppi1, ImppAST, [Not (Imp [Not c; y]); c; y], [], []);
                  (resi1, ResoAST, [lhs; c; Not (Imp [Not c; y])], [iteni1; imppi1], []);
                  (iteni2, Iten2AST, [lhs; Not c; Not x], [], []);
                  (imppi2, ImppAST, [Not (Imp [c; x]); Not c; x], [], []);
                  (resi2, ResoAST, [lhs; Not c; Not (Imp [c; x])], [iteni2; imppi2], []);
                  (andpi1, AndpAST, [Not rhs; Imp [c; x]], [], ["0"]);
                  (andpi2, AndpAST, [Not rhs; Imp [Not c; y]], [], ["1"]);
                  (generate_id (), ResoAST, [rhs], [resi1; resi2; andpi1; andpi2; b2ai], [])] in 
       (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* forall x_1, ..., x_n. F <-> ~ exists x_1, ..., x_n. ~F *)
       | [Eq (Forall _, _)] -> raise (Debug ("| process_simplify: forall case of connective_def at id "^i^" not supported |"))
       | [Eq _] -> raise (Debug ("| process_simplify: unexpected form of equivalence for connective_def at id "^i^" |"))
       | _ -> raise (Debug ("| process_simplify: expecting connective_def to derive a singleton equivalence at id "^i^" |")))
  (* t1 = t2 <-> x *)
  | (i, EqualsimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
       (* t = t <-> T *)
       | [Eq ((Eq (t, t') as lhs), (True as rhs))] when t = t' ->
       (*
          LTR:
          ---true
           T   
       *)
         let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
         let c' = try process_cl cl with
                  | Form.NotWellTyped frm -> raise (Debug ("| process_simplify: formula "^
                       (Form.pform_to_string frm)^" is not well-typed at id "^i^" |")) in
         let is_frm =
         (match c' with
          | l :: _ ->
             (try (match Form.pform l with
                   | Fapp (Fiff, args) -> is_iff (Array.get args 0)
                   | _ -> raise (Debug ("| process_simplify: expecting head of clause to be an iff at id "^i^" |"))) with
              | Form.NotWellTyped frm -> raise (Debug ("| process_cong: formula "^(Form.pform_to_string frm)^" is not well-typed at id "^i^" |")))
          | _ -> raise (Debug ("| process_simplify: expecting clause for eq_simplify to be a singleton at id "^i^" |"))) in
         let b2a =
            (* equality over terms *)
            (if is_frm then
              (* equality over formulas:
                RTL:
                ---------eqn1  ---------eqn2
                x = x, ~x       x = x, x
                ------------------------res
                           x = x
              *)
              let eqn1i = generate_id () in
              let eqn2i = generate_id () in
              [(eqn1i, Equn1AST, [lhs; Not t], [], []);
               (eqn2i, Equn2AST, [lhs; t], [], []);
               (i, ResoAST, [lhs], [eqn1i; eqn2i], [])]
            else
              (* equality over terms:
                RTL:
                -----refl
                x = x
              *)
              [(generate_id (), EqreAST, [lhs], [], [])]) in
         (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl
       (* t1 = t2 <-> F, when t1, t2 are different numeric constants *)
       | [Eq ((Eq (Int t1, Int t2) as lhs), (False as rhs))] when t1 <> t2 ->
       (* 
          LTR:
          -------asmp   ----------la_generic
          t1 = t2       ~(t1 = t2)
          ------------------------res
                    []
               -----------weaken
                    F
       *)
         let a2bi = generate_id () in
         let lagei = generate_id () in
         let resi = generate_id () in
         let a2b = [(lagei, LageAST, [Not lhs], [], []);
                    (resi, ResoAST, [], [a2bi; lagei], []);
                    (generate_id (), WeakenAST, [rhs], [resi], [])] in
       (*
           RTL:
           ---asmp  ----false
            F        ~F
            -----------res
                []
            ----------weaken
             t1 = t2
       *)
        let b2ai = generate_id () in
        let fi = generate_id () in
        let resi = generate_id () in
        let b2a = [(fi, FalsAST, [Not False], [], []);
                   (resi, ResoAST, [], [b2ai; fi], []);
                   (generate_id (), WeakenAST, [lhs], [resi], [])] in
        (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       (* ~(t = t) <-> F, if t is a numeric constant *)
       | [Eq ((Not (Eq (Int t, Int t')) as lhs), (False as rhs))] when t = t' ->
      (*
          LTR:
          --------asmp  ------la_generic
          ~(t = t)      t = t
          -------------------res
                   []
              ------------weaken
                   F
      *)
       let a2bi = generate_id () in
       let lagei = generate_id () in
       let resi = generate_id () in
       let a2b = [(lagei, LageAST, [Eq (Int t, Int t)], [], []);
                  (resi, ResoAST, [], [a2bi; lagei], []);
                  (generate_id (), WeakenAST, [rhs], [resi], [])] in
      (*
         RTL:
         ---asmp  ----false
          F        ~F
          -----------res
               []
          ----------weaken
             t = t
      *)
       let b2ai = generate_id () in
       let fi = generate_id () in
       let resi = generate_id () in
       let b2a = [(fi, FalsAST, [Not False], [], []);
                  (resi, ResoAST, [], [b2ai; fi], []);
                  (generate_id (), WeakenAST, [lhs], [resi], [])] in
       (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
       | _ -> raise (Debug ("| process_simplify: expecting argument of eq_simplify to be an equivalence at id "^i^" |"))
      )
  (* ac_simp: x <-> y, where 
       - x contains arbitrarily nested `and`s and `or`s of literals
       - all `and`s and `or`s from `x` are flattened in `y`
       - all duplicates are removed in `y` (after flattening)
  
  | (i, AcsimpAST, cl, p, a) :: tl ->
      (match (get_expr_cl cl) with
      | [Eq (x, y)] ->
        let a2bi = generate_id () in
        let b2ai = generate_id () in
        let a2b = [(generate_id (), AcsimpAST, [y], [a2bi], [])] in
        let b2a = [(generate_id (), AcsimpAST, [x], [b2ai], [])] in
         (simplify_to_subproof i a2bi b2ai x y a2b b2a) @ process_simplify tl
      | _ -> raise (Debug ("| process_simplify: expecting argument of ac_simp to be an equivalence at id "^i^" |"))
      )*)
  (* all_simplify represents rewrite rules from cvc5. We assume that these come 
     from a version that uses the DSL which will specify cvc5 rewrites in terms
     of veriT rewrites (the rest of the simp rules) as specified by the arg of the
     rule, which we need to pattern-match on *)
  | (i, AllsimpAST, cl, p, a) :: tl ->
   (match a with
    | a1 :: _ when (compare_sub (String.trim a1) "and_simplify") -> process_simplify ((i, AndsimpAST, cl, p, []) :: tl)
    | a1 :: _ when (compare_sub (String.trim a1) "or_simplify") -> process_simplify ((i, OrsimpAST, cl, p, []) :: tl)
    | a1 :: _ when (compare_sub (String.trim a1) "not_simplify") -> process_simplify ((i, NotsimpAST, cl, p, []) :: tl)
    | a1 :: _ when (compare_sub (String.trim a1) "implies_simplify") -> process_simplify ((i, ImpsimpAST, cl, p, []) :: tl)
    | a1 :: _ when (compare_sub (String.trim a1) "equiv_simplify") -> process_simplify ((i, EqsimpAST, cl, p, []) :: tl)
    | a1 :: _ when (compare_sub (String.trim a1) "bool_simplify") -> process_simplify ((i, BoolsimpAST, cl, p, []) :: tl)
    | a1 :: _ when (compare_sub (String.trim a1) "connective_def") -> process_simplify ((i, ConndefAST, cl, p, []) :: tl)
    | a1 :: _ when (compare_sub (String.trim a1) "eq_simplify") -> process_simplify ((i, EqualsimpAST, cl, p, []) :: tl)
    | a1 :: _ when (compare_sub (String.trim a1) "ite_simplify") -> process_simplify ((i, ItesimpAST, cl, p, []) :: tl)
    | a1 :: _ -> raise (Debug ("| process_simplify: DSL failure! Expecting arg of all_simplify step to have a rewrite rule via DSL at id "^i^", instead I have "^a1^" |"))
    | [] -> 
      match cl with
      | [Eq ((x as lhs), (False as rhs))] ->
      (*
          LTR:
          --------asmp  ------la_generic
              x           ~x
          -------------------res
                   []
              ------------weaken
                   F
      *)
       let a2bi = generate_id () in
       let lagei = generate_id () in
       let resi = generate_id () in
       let a2b = [(lagei, LageAST, [Not x], [], []);
                  (resi, ResoAST, [], [a2bi; lagei], []);
                  (generate_id (), WeakenAST, [rhs], [resi], [])] in
     (*
        RTL:
        ---asmp  ----false
         F        ~F
         -----------res
              []
         ----------weaken
              x
     *)
       let b2ai = generate_id () in
       let fi = generate_id () in
       let resi = generate_id () in
       let b2a = [(fi, FalsAST, [Not False], [], []);
                  (resi, ResoAST, [], [b2ai; fi], []);
                  (generate_id (), WeakenAST, [lhs], [resi], [])] in
       (simplify_to_subproof i a2bi b2ai lhs rhs a2b b2a) @ process_simplify tl
      | [Eq ((x as lhs), (True as rhs))] ->
      (*
          LTR:
          ---true
           T   
      *)
       let a2b = [(generate_id (), TrueAST, [rhs], [], [])] in
      (*
          RTL:
          ---la_generic
           x   
      *)
       let b2a = [(generate_id (), LageAST, [lhs], [], [])] in
       (simplify_to_subproof i (generate_id ()) (generate_id ()) lhs rhs a2b b2a) @ process_simplify tl
      (* Assuming that we catch all rewrites except generic LIA rewrites, for which we use this catch-all LIA rule *)
      | _ -> (i, LiaRewriteAST, cl, p, a) :: process_simplify tl)
  | h :: tl -> h :: process_simplify tl
  | nil -> nil
  

(* Process holes in proof. cvc5 produces holes with arg ARITH_POLY_NORM which are tautologies 
   that can be sent to Micromega *)
let rec process_hole (c : certif) : certif = 
  match c with
  | (i, HoleAST, cl, p, a) :: tl when 
      (if (List.length a > 0) then 
        (compare_sub (String.trim (List.hd a)) "ARITH_POLY_NORM")
      else false) -> (i, ArithpolynormAST, cl, p, a) :: process_hole tl
  | h :: tl -> h :: process_hole tl
  | [] -> []


(* Final processing and linking of AST *)
(* Ordering constraint:
   1. process_proj before process_subproof because subproof turns all projection
      rules to tautological rules and needs them to have arguments for this. To remove 
      constraint, search for projection within `extend_cl`. *)
let preprocess_certif (c: certif) : certif =
  (* Printf.printf ("Certif before preprocessing: \n%s\n") (string_of_certif c); *)
  try 
  (let c1 = store_shared_terms c in
  (* Printf.printf ("Certif after storing shared terms: \n%s\n") (string_of_certif c1); *)
  let c2 = process_fins c1 in
  (* Printf.printf ("Certif after process_fins: \n%s\n") (string_of_certif c2); *)
  let c3 = process_hole c2 in
  (* Printf.printf ("Certif after process_hole: \n%s\n") (string_of_certif c3); *)
  let c4 = process_notnot c3 in
  (* Printf.printf ("Certif after process_notnot: \n%s\n") (string_of_certif c4); *)
  let c5 = process_same c4 in
  (* Printf.printf ("Certif after process_same: \n%s\n") (string_of_certif c5); *)
  let c6 = process_cong c5 in
  (* Printf.printf ("Certif after process_cong: \n%s\n") (string_of_certif c6); *)
  let c7 = process_trans c6 in
  (* Printf.printf ("Certif after process_trans: \n%s\n") (string_of_certif c7); *)
  let c8 = process_simplify c7 in
  (* Printf.printf ("Certif after process_simplify: \n%s\n") (string_of_certif c8); *)
  let c9 = process_proj c8 in
  (* Printf.printf ("Certif after process_proj: \n%s\n") (string_of_certif c9); *)
  let c10 = process_subproof c9 in
  (* Printf.printf ("Certif after process_subproof: \n%s\n") (string_of_certif c10); *)
  c10) with
  | Debug s -> raise (Debug ("| VeritAst.preprocess_certif: failed to preprocess |"^s))

let rec process_certif (c : certif) : VeritSyntax.id list =
  match c with
  | (i, r, c, p, a) :: t ->
      let i' = VeritSyntax.id_of_string i in
      let r' = try process_rule r with
               | Debug s -> raise (Debug 
                  ("| VeritAst.process_certif: can't process clause at id "
                  ^i^"|"^s)) in
      let c' = try process_cl c with
               | Form.NotWellTyped p -> raise (Debug ("VeritAst.process_certif: formula "^
                            (Form.pform_to_string p)^" is not well-typed at id "^i))
               | Debug s -> raise (Debug 
                  ("| VeritAst.process_certif: can't process clause at id "
                  ^i^" |"^s)) in
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