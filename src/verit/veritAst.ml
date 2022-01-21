type term = 
  | True
  | False
  | Neg of term
  | And of term list
  | Or of term list
  | Imp of term list
  | Xor of term list
  | Ite of term * term * term
  | Forall of (string * typ) list * term
  | Int of int (* change to bigint *)
  | Eq of term * term
  | App of string * (term list)
  | Var of string
  | STerm of string (* Shared term *)
  | NTerm of string * term (* Named term *)

type typ = 
  | Int

type clause = term list
type id = string
type params = id list
type args = (term * term) list
type rule = 
  | Assume of 
  | True
  | Fals
  | Notnot
  | Threso
  | Reso
  | Taut
  | Cont
  | Refl
  | Trans
  | Cong
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
  | Conndef
  | Andsimp
  | Orsimp
  | Notsimp
  | Impsimp
  | Eqsimp
  | Boolsimp
  | Acsimp
  | Itesimp
  | Equalsimp
  | Distelim
  | Lage
  | Liage
  | Lata
  | Lade
  | Divsimp
  | Prodsimp
  | Uminussimp
  | Minussimp
  | Sumsimp
  | Compsimp
  | Larweq
  | Bind
  | Fins
  | Qcnf
  | Ident
  | Hole
  | Anchor
  | Subproof of certif

and step = (id, rule, clause, params, args)
and certif = step list



(* Restructure certif to be a recursive tree *)
type certif =
  | Leaf of step
  | Tree of certif * step * certif


(* Remove notnot rule from certificate *)
let get_id (s : step ) : id = 
match s with
| (i, _, _, _, _) -> i

(* Remove element from list *)
let rec remove x l =
  match l with
  | h :: t -> if h == x then remove x t else h :: (remove x t)
  | [] -> []

  (* Remove premise from all resolutions in certif *)
let rec remove_res_premise (i : id) (c : certif) : certif =
  match c with
  | (i, r, c, p, a) :: t -> 
      match r with
      | Reso | Threso -> (i, r, c, (remove i p), a) :: (remove_res_premise t)
      | _ -> (i, r, c, p, a) :: (remove_res_premise t)

(* Soundly remove all notnot rules from certificate *)
let rec remove_notnot (c : certif) : certif = 
  match c with
  | (i, r, _, _, _) :: t ->
      match r with
      | Notnot -> remove_notnot (remove_res_premise i t)
      | _ -> h :: remove_notnot t
  | [] -> []