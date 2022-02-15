open SmtBtype
open SmtAtom
open SmtForm
open VeritSyntax

type typ = 
  | Int
  | Bool

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
type args = id list
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
  | SubproofAST of certif
and step = id * rule * clause * params * args
and certif = step list

let mk_cl (ts : term list) : clause = ts
let mk_step (s : (id * rule * clause * params * args)) : step = s
let mk_cert (c : step list) : certif = c
let mk_args (a : id list) : args = a

let rec get_cl (i : id) (c : certif) : clause option = 
  match c with
  | (i', r, c, p, a) :: t -> if i = i' then Some c else get_cl i t
  | [] -> None


(* Convert certificates to strings for debugging *)
let string_of_rule (r : rule) : string =
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
  | AnchorAST -> "AnchorAST"
  | SubproofAST _ -> "SubproofAST"

let string_of_typ (t : typ) : string =
  match t with
  | Int -> "Int"
  | Bool -> "Bool"

let concat_sp x y = x^" "^y

let rec string_of_term (t : term) : string = 
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
  | NTerm (s, t) -> s^" :named "^(string_of_term t)
  | Int i -> string_of_int i
  | Lt (t1, t2) -> (string_of_term t1)^" < "^(string_of_term t2)
  | Leq (t1, t2) -> (string_of_term t1)^" <= "^(string_of_term t2)
  | Gt (t1, t2) -> (string_of_term t1)^" > "^(string_of_term t2)
  | Geq (t1, t2) -> (string_of_term t1)^" >= "^(string_of_term t2)
  | UMinus t -> "-"^(string_of_term t)
  | Plus (t1, t2) -> (string_of_term t1)^" + "^(string_of_term t2)
  | Minus (t1, t2) -> (string_of_term t1)^" - "^(string_of_term t2)
  | Mult (t1, t2) -> (string_of_term t1)^" * "^(string_of_term t2)

let string_of_clause (c : clause) =
  let args = List.fold_left concat_sp "" (List.map string_of_term c) in
  "(cl "^args^")"

let rec string_of_certif (c : certif) : string = 
  match c with
  | (i, r, c, p, a) :: t -> 
      let r' = string_of_rule r in
      let c' = string_of_clause c in
      let p' = List.fold_left concat_sp "" p in
      let a' = List.fold_left concat_sp "" a in
      "("^i^", "^r'^", "^c'^", ["^p'^"], ["^a'^"])\n"^(string_of_certif t)
  | [] -> ""


(* Convert Cong to Eqco + Reso for congruences over functions *)

(*let rec replace_cong (c : certif) : certif = 
  match c with
  | (i, r, c, p, a) :: t -> 
      (match r with
       | CongAST -> match c with)*)


(* Remove notnot rule from certificate *)

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

(* Soundly remove all notnot rules from certificate *)
let rec remove_notnot (c : certif) : certif = 
  match c with
  | (i, r, cl, p, a) :: t ->
      (match r with
      | NotnotAST -> remove_notnot (remove_res_premise i t)
      | _ -> (i, r, cl, p, a) :: remove_notnot t)
  | [] -> []


(* Convert the sequence of ids in the steps to sequential integers.
   Do this after finishing all the transformations to the certificates 
   that might add/remove steps *)
let ids : (string, string) Hashtbl.t = Hashtbl.create 17
let get_id s = Hashtbl.find ids s
let add_id s i = Hashtbl.add ids s i
let clear_ids () = Hashtbl.clear ids
let to_sequential_ids (c : certif) : certif =
  let rec aux (z : int) (c : certif) : certif = 
    match z, c with
    | z, (i, r, c, p, a) :: t -> add_id i (string_of_int z);
        let z' = string_of_int z in
        let p' = List.map (fun x -> get_id x) p in
        (z', r, c, p', a) :: aux (z+1) t
    | z, [] -> []
  in (clear_ids (); aux 1 c)


(* Convert an AST to a list of clauses *)

let process_typ (t : typ) : SmtBtype.btype =
  match t with
  | Int -> TZ
  | Bool -> Tbool

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
  | STerm s -> get_solver s
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
  | AnchorAST -> Hole
  | SubproofAST c -> Hole


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
let rec process_cong (c : certif) : certif = 
  let process_cong_aux (c : certif) (cog : certif) : certif = 
    match c with
    | (i, r, c, p, a) :: t ->
        (match r with
        | CongAST ->
            let i' = VeritSyntax.id_of_string i in
            let r' = process_rule r in
            let c' = process_cl c in
            let p' = List.map (VeritSyntax.id_of_string) p in
            let a' = List.map (VeritSyntax.id_of_string) a in
            (match c' with
            | l::_ -> 
                (* congruence over functions *)
                if is_eq l then
                  let new_id = VeritSyntax.generate_id () in
                  (* get premises and convert from clauses to formulas *)
                  let prems = List.map (fun x -> (match (get_cl x cog) with
                                                 | Some x -> Not (List.hd x)
                                                 | None -> assert false)) p in
                  (* perform application of eq_congruent to 
                   get a CNF form of the rule application *)
                  let new_cl = mk_cl (prems @ c) in
                  (* then, resolve out all the premises from the CNF so only 
                   the conclusion is left *)
                  (VeritSyntax.string_of_id new_id, EqcoAST, new_cl, [], []) ::
                  (i, ResoAST, c, new_id :: p, a) :: 
                  (* add the resolution *) process_cong t
                else
                  (* congruence over predicates*)
                  (i, r, c, p, a) :: process_cong t
              | _ -> assert false)
        | _ -> let c' = process_cl c in 
               (i, r, c, p, a) :: process_cong t)
    | [] -> []
    in process_cong_aux c c


(* TODO: Rules with args need to be parsed properly *)
(* Final processing and linking of AST *)
let preprocess_certif (c: certif) : certif =
  let c1 = remove_notnot c in
  let c2 = process_cong c1 in
  c2

let rec process_certif (c : certif) : VeritSyntax.id list =
  match c with
  | (i, r, c, p, a) :: t ->
      let i' = VeritSyntax.id_of_string i in
      let r' = process_rule r in
      let c' = process_cl c in
      let p' = List.map (VeritSyntax.id_of_string) p in
      let a' = List.map (VeritSyntax.id_of_string) a in
      (* Must do this in this order to avoid side effects *)
      let res = mk_clause (i', r', c', p', a') in
      (* Process next step for linking *)
      let t' = process_certif t in
      if List.length t' > 0 then (
        let x = List.hd t' in
        SmtTrace.link (get_clause_exception ("linking clause "^(string_of_id res)^" in VeritAst.process_certif") res) 
                      (get_clause_exception ("linking clause "^(string_of_id x)^" in VeritAst.process_certif") x)
        ) else ();
      res :: t'
  | [] -> []