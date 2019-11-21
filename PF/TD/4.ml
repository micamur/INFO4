(*
ABR : suppression d'un élément

1. Chercher l'élément maximum d'un ABR
2. "Supprimer l'élément maximum d'un ABR
3. "Supprimer" l'élément à la racine
4. "Supprimer" un élément dans un ABR
*)

type arbin = V | N of arbin * int * arbin;;

exception ArbreVide;;

(* 1 *)

let maxArbin (abr : arbin) : int =
  let aux (abr : arbin) : int =
    | N(_, f, V) -> f
    | N(_, _, fd) -> (aux fd)
  in
  match abr with
  | V -> raise ArbreVide
  | n -> (aux n)
;;

(* 2 *)

let supMaxArbin (abr : arbin) : arbin =
  let rec aux (abr : arbin) : int =
    match abr with
    | N(fg, x, N(fdg, y, V)) -> N(fg, x, fdg)
    | N(fg, x, fd) -> N(fg, x, (aux fd))
  in
  match abr with
  | V -> raise ArbreVide
  | n -> (aux n)
;;

let rec supMaxAux g x d : int * arbin =
    match d with
    | V -> (x, g)
    | N(gd, xd, dd) ->
      let (m, supd) = supMaxAux gd xd dd in
      (m, N(g, x, supd))
;;

let supMaxArbin2 (abr : arbin) : int * arbin =
  match abr with
  | V -> raise ArbreVide
  | N(g, x, d) -> (supMaxAux g, x, d)
;;

(* 3 *)

let supRacine (a : arbin) =
  match a with
  | V -> raise ArbreVide
  | N(g, x, d) ->
    match g with
    | V -> d
    | N(gg, xg, dg) ->
      let (m, supg) = supMaxAux gg xg dg in
      N(supg, m, d)