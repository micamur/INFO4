
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b



type sumbool =
| Left
| Right

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val string_dec : string -> string -> sumbool **)

let rec string_dec = (=)

type word = int32

type ident = string

type oper1 =
| Bneg

type oper2 =
| Shift_l
| Shift_r
| Wxor
| Wand
| Band
| Bor
| Cmp_eq

type expr =
| Ent32 of word
| Bool of bool
| Var of ident
| Op1 of oper1 * expr
| Op2 of oper2 * expr * expr

(** val default_w : word **)

let default_w = Int32.zero

(** val zeros_bit : bool -> word **)

let zeros_bit = fun b -> if b then 1l else 0l

(** val bit_poids_faible : word -> bool **)

let bit_poids_faible = fun x -> Int32.logand x 1l = 1l

type etat = (ident, word) prod list

(** val get : etat -> ident -> word **)

let rec get s x =
  match s with
  | [] -> default_w
  | p::s0 ->
    let Pair (i, w) = p in
    (match string_dec i x with
     | Left -> w
     | Right -> get s0 x)

(** val shift_l1 : word -> word **)

let shift_l1 = (fun x -> Int32.shift_left x 1)

(** val shift_r1 : word -> word **)

let shift_r1 = (fun x -> Int32.shift_right x 1)

(** val nat_of_word : word -> int **)

let rec nat_of_word = Int32.to_int

(** val iter : int -> (word -> word) -> word -> word **)

let rec iter = fun n f x -> if n = 0 then x else f (iter (n-1) f x)

(** val shift_l : word -> word -> word **)

let shift_l w1 w2 =
  iter (nat_of_word w1) shift_l1 w2

(** val shift_r : word -> word -> word **)

let shift_r w1 w2 =
  iter (nat_of_word w1) shift_r1 w2

(** val wxor : word -> word -> word **)

let wxor = Int32.logxor

(** val wand : word -> word -> word **)

let wand = Int32.logand

(** val cmp_eq : word -> word -> bool **)

let rec cmp_eq = (=)

type tts =
| Tmot
| Tbool

type valeur =
| Vb of bool
| Vw of word

type resul = valeur option

(** val lift1_bb : (bool -> bool) -> resul -> resul **)

let lift1_bb f = function
| Some v -> (match v with
             | Vb b -> Some (Vb (f b))
             | Vw _ -> None)
| None -> None

(** val lift2_www : (word -> word -> word) -> resul -> resul -> resul **)

let lift2_www f r1 r2 =
  match r1 with
  | Some v ->
    (match v with
     | Vb _ -> None
     | Vw b1 ->
       (match r2 with
        | Some v0 ->
          (match v0 with
           | Vb _ -> None
           | Vw b2 -> Some (Vw (f b1 b2)))
        | None -> None))
  | None -> None

(** val lift2_bbb : (bool -> bool -> bool) -> resul -> resul -> resul **)

let lift2_bbb f r1 r2 =
  match r1 with
  | Some v ->
    (match v with
     | Vb b1 ->
       (match r2 with
        | Some v0 ->
          (match v0 with
           | Vb b2 -> Some (Vb (f b1 b2))
           | Vw _ -> None)
        | None -> None)
     | Vw _ -> None)
  | None -> None

(** val lift2_wwb : (word -> word -> bool) -> resul -> resul -> resul **)

let lift2_wwb f r1 r2 =
  match r1 with
  | Some v ->
    (match v with
     | Vb _ -> None
     | Vw b1 ->
       (match r2 with
        | Some v0 ->
          (match v0 with
           | Vb _ -> None
           | Vw b2 -> Some (Vb (f b1 b2)))
        | None -> None))
  | None -> None

(** val op1_resul : oper1 -> resul -> resul **)

let op1_resul _ =
  lift1_bb negb

(** val op2_resul : oper2 -> resul -> resul -> resul **)

let op2_resul = function
| Shift_l -> lift2_www shift_l
| Shift_r -> lift2_www shift_r
| Wxor -> lift2_www wxor
| Wand -> lift2_www wand
| Band -> lift2_bbb (fun b1 b2 -> if b1 then b2 else false)
| Bor -> lift2_bbb (fun b1 b2 -> if b1 then true else b2)
| Cmp_eq -> lift2_wwb cmp_eq

(** val eval_expr : etat -> expr -> resul **)

let rec eval_expr s = function
| Ent32 w -> Some (Vw w)
| Bool b -> Some (Vb b)
| Var i -> Some (Vw (get s i))
| Op1 (o, e0) -> op1_resul o (eval_expr s e0)
| Op2 (o, e1, e2) -> op2_resul o (eval_expr s e1) (eval_expr s e2)

type roptim = word

(** val lift1_opt_bb : (bool -> bool) -> roptim -> roptim **)

let lift1_opt_bb f r =
  zeros_bit (f (bit_poids_faible r))

(** val lift2_opt_bbb :
    (bool -> bool -> bool) -> roptim -> roptim -> roptim **)

let lift2_opt_bbb f r1 r2 =
  zeros_bit (f (bit_poids_faible r1) (bit_poids_faible r2))

(** val lift2_opt_wwb :
    (word -> word -> bool) -> roptim -> roptim -> roptim **)

let lift2_opt_wwb f r1 r2 =
  zeros_bit (f r1 r2)

(** val op1_roptim : oper1 -> roptim -> roptim **)

let op1_roptim _ =
  lift1_opt_bb negb

(** val op2_roptim : oper2 -> roptim -> roptim -> roptim **)

let op2_roptim = function
| Shift_l -> shift_l
| Shift_r -> shift_r
| Wxor -> wxor
| Wand -> wand
| Band -> lift2_opt_bbb (fun b1 b2 -> if b1 then b2 else false)
| Bor -> lift2_opt_bbb (fun b1 b2 -> if b1 then true else b2)
| Cmp_eq -> lift2_opt_wwb cmp_eq

(** val evoptim : etat -> expr -> roptim **)

let rec evoptim s = function
| Ent32 w -> w
| Bool b -> zeros_bit b
| Var i -> get s i
| Op1 (o, e0) -> op1_roptim o (evoptim s e0)
| Op2 (o, e1, e2) -> op2_roptim o (evoptim s e1) (evoptim s e2)

(** val type_sortie_1 : oper1 -> tts **)

let type_sortie_1 _ =
  Tbool

(** val type_sortie_2 : oper2 -> tts **)

let type_sortie_2 = function
| Band -> Tbool
| Bor -> Tbool
| Cmp_eq -> Tbool
| _ -> Tmot

(** val type_entree_1 : oper1 -> tts **)

let type_entree_1 _ =
  Tbool

(** val type_entree1_2 : oper2 -> tts **)

let type_entree1_2 o = match o with
| Cmp_eq -> Tmot
| _ -> type_sortie_2 o

(** val type_entree2_2 : oper2 -> tts **)

let type_entree2_2 =
  type_entree1_2

(** val type_tete : expr -> tts **)

let type_tete = function
| Bool _ -> Tbool
| Op1 (o, _) -> type_sortie_1 o
| Op2 (o, _, _) -> type_sortie_2 o
| _ -> Tmot

(** val eq_types : tts -> tts -> bool **)

let eq_types t1 t2 =
  match t1 with
  | Tmot -> (match t2 with
             | Tmot -> true
             | Tbool -> false)
  | Tbool -> (match t2 with
              | Tmot -> false
              | Tbool -> true)

(** val bien_type : expr -> bool **)

let rec bien_type = function
| Op1 (o, e0) ->
  if bien_type e0 then eq_types (type_tete e0) (type_entree_1 o) else false
| Op2 (o, e1, e2) ->
  if if bien_type e1 then bien_type e2 else false
  then if eq_types (type_tete e1) (type_entree1_2 o)
       then eq_types (type_tete e2) (type_entree2_2 o)
       else false
  else false
| _ -> true
