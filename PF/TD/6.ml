(* 6. MODULES ET FONCTEURS *)

(* Exercice 78 : Module Exam 2013 *)

(*1*)

(* Il est impossible de savoir à l'extérieur du module  qui a déjà voté ni quel est le vote de quelqu'un, 
   car il n'existe aucune fonction de type t -> electeur -> bool ou t -> electeur -> candidat *)

(*2*)

type electeur = int;;
type candidat = A | B;;
type t = (electeur * candidat) list;;

let vide unit : t = [];;

let rec voter (e : electeur) (c : candidat) (u : t) : t =
  match u with
  | [] -> [(e, c)]
  | (ei, ci)::rl ->
     if (ei = e) then (e, c)::rl else (ei, ci)::(voter e c rl)
;;

let rec depouiller (u : t) : (int * int) =
  match u with
  | [] -> (0, 0)
  | (ei, ci)::rl ->
     let (a, b) = (depouiller rl) in
     (match ci with
      | A -> (a+1, b)
      | B -> (a, b+1))
;;

let rec vainqueur (u : t) : candidat option =
  let (a, b) = (depouiller u) in
  if (a > b) then Some A else if (a < b) then Some B else None
;;

let u1 : t = vide ();;
let u2 : t = (voter 1 A u1);;
let u3 : t = (voter 2 B u2);;
let u4 : t = (voter 1 B u3);;

depouiller u1;;
depouiller u2;;
depouiller u3;;
depouiller u4;;

vainqueur u1;; (*vide*)
vainqueur u2;; (*A*)
vainqueur u3;; (*égalité*)
vainqueur u4;; (*B*)

(* Exercice 79 : Module et foncteur Exam 2014 *)

(*1*)

type cle = string;;
type 'a mem = ('a * cle) list;;

let egal (c1 : cle) (c2 : cle) : bool = c1 = c2;;

let memVide : 'a mem = [];;

let estVide (m : 'a mem) : bool =
  match m with
  | [] -> true
  | _ -> false
;;

let rec inserer (m : 'a mem) (e : 'a) (c : cle) : 'a mem =
  match m with
  | [] -> [(e, c)]
  | head::rl -> head::(inserer rl e c)
;;

let rec extraire (m : 'a mem) (c : cle) : 'a list =
  match m with
  | [] -> []
  | (ei, ci)::rl ->
     if (egal ci c) then ei::(extraire rl c) else (extraire rl c)
;;

let rec extraire1 (m : 'a mem) (c : cle) : 'a option =
  match m with
  | [] -> None
  | (ei, ci)::rl ->
     if (egal ci c) then Some ei else (extraire1 rl c)
;;

(*
Là on renvoie une liste de ('a * cle) au lieu de renvoyer une liste de 'a.

let extraire (m : 'a mem) (c : cle) : 'a list =
  let predicat (ei, ci : 'a * cle) : bool = (ci = c) in
  List.filter predicat m
;;
*)

let mi1 : int mem = memVide;;
estVide mi1;;
let mi2 : int mem = inserer mi1 1 "un";;
let mi3 : int mem = inserer mi2 2 "deux";;
let mi4 : int mem = inserer mi3 2 "deux";;
extraire mi4 "un";;
extraire mi4 "deux";;
extraire mi4 "trois";;
extraire1 mi4 "un";;
extraire1 mi4 "deux";;
extraire1 mi4 "trois";;

(*2*)

type 'a mem2 = (cle * ('a list)) list;;

let memVidebis : 'a mem2 = [];;

let estVidebis (m : 'a mem2) : bool =
  match m with
  | [] -> true
  | _ -> false
;;

let rec insererbis (m : 'a mem2) (e : 'a) (c : cle) : 'a mem2 =
  match m with
  | [] -> [(c, [e])]
  | (ci, li)::rl ->
     if (egal ci c) then
       let rec insererbisaux (laux : 'a list) (eaux : 'a) : 'a list =
         match laux with
         | [] -> [e]
         | ei::rl -> ei::(insererbisaux rl eaux)
       in
       let (c2, l2) : (cle * 'a list) = (ci, (insererbisaux li e))
       in
       (c2, l2)::rl
     else
       (ci, li)::(insererbis rl e c)
;;

let rec extrairebis (m : 'a mem2) (c : cle) : 'a list =
  match m with
  | [] -> []
  | (ei, ci)::rl -> (*TODO*) []
;;

let rec extraire1bis (m : 'a mem2) (c : cle) : 'a option =
  match m with
  | [] -> None
  | (ei, ci)::rl -> (*TODO*) None
;;


let mi1bis : int mem2 = memVidebis;;
estVidebis mi1bis;;
let mi2bis : int mem2 = insererbis mi1bis 1 "un";;
let mi3bis : int mem2 = insererbis mi2bis 2 "deux";;
let mi4bis : int mem2 = insererbis mi3bis 2 "deux";;
extrairebis mi4bis "un";;
extrairebis mi4bis "deux";;
extrairebis mi4bis "trois";;
extraire1bis mi4bis "un";;
extraire1bis mi4bis "deux";;
extraire1bis mi4bis "trois";;
