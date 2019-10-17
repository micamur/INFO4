(* 2. MANIPULATION DE LISTES *)

(* 2.1. LES DÉMÉNAGEURS OCAML *)

(* Exercice 17. Types *)

type contenu = Meuble | Objet | Cadre | Plante;;
type solidite = Fragile | Robuste | Normal;;
type paquet = contenu * solidite * int;;

(* Exercice 18. Fragiles *)

let rec fragiles : paquet list -> int =
  fun l ->
  match l with
  | [] -> 0
  | (c, s, i)::rl -> (fragiles rl) + (match s with
                      | Fragile -> 1
                      | _ -> 0);;

let pMR21 : paquet = (Meuble, Robuste, 21);;
let pON8 : paquet = (Objet, Normal, 8);;
let pPF1 : paquet = (Plante, Fragile, 1);;
let pCF3 : paquet = (Cadre, Fragile, 3);;
let inventaire : paquet list = pPF1::pCF3::pON8::pMR21::[];;

fragiles inventaire;; (* 2 *)

(* Exercice 19. Légers *)

let rec legers : int -> paquet list -> paquet list =
  fun poids ->
  fun l ->
  match l with
  | [] -> []
  | (c, s, i)::rl when i <= poids -> (c, s, i)::(legers poids rl)
  | p::rl -> legers poids rl;;

legers 7 inventaire;;

(* Exercice 20. Poids plantes *)

let rec poids_plantes : paquet list -> int =
  fun l ->
  match l with
  | [] -> 0
  | (c, s, i)::rl -> poids_plantes rl + (match c with
                      | Plante -> i
                      | _ -> 0);;

poids_plantes inventaire;; (* [pPF1; pCF3] *)

(* Exercice 21. Exposition *)

let rec exposition : paquet list -> paquet list =
  fun l ->
  match l with
  | [] -> []
  | (c, s, i)::rl -> (match c with
                      | Cadre -> exposition rl
                      | _ -> (c, s, i)::(exposition rl));;

exposition inventaire;; (* [pPF1;pON8;pMR21] *)

(* Exercice 22. Inventorie *)

let rec inventorie : paquet -> paquet list -> paquet list =
  fun (pc, ps, pi) ->
  fun l ->
  match l with
  | [] -> [pc, ps, pi]
  | (c, s, i)::rl when pi <= i -> (pc, ps, pi)::(c, s, i)::rl
  | (c, s, i)::rl -> (c, s, i)::(inventorie (pc, ps, pi) rl);;

let pOF0 : paquet = (Objet, Fragile, 0);;
inventorie pOF0 inventaire;;                (* [pOF0;pPF1;pCF3;pON8;pMR21] *)
let pOF2 : paquet = (Objet, Fragile, 2);;
inventorie pOF2 inventaire;;                (* [pPF1;pOF2;pCF3;pON8;pMR21] *)
let pOF22 : paquet = (Objet, Fragile, 22);;
inventorie pOF22 inventaire;;               (* [pPF1;pCF3;pON8;pMR21;pOF22] *)

(* Exercice 23. Dromadaire *)

let rec dromadaire : paquet list -> paquet =
  fun l ->
  match l with
  | [] -> failwith "Liste vide"
  | [p] -> p
  | (c1, s1, i1)::(c2, s2, i2)::rl ->
     if (i1 > i2)
     then (dromadaire ((c1, s1, i1)::rl))
     else (dromadaire ((c2, s2, i2)::rl))
;;

dromadaire inventaire;;                                           (* pMR21 *)
dromadaire ((Objet, Robuste, 666)::pPF1::pCF3::pON8::pMR21::[]);; (* (Objet, Robuste, 666) *)

(* Exercice 24. Chameau *)

let rec chameau : paquet list -> paquet list =
  fun l ->
  match l with
  | [] -> failwith "Liste vide"
  | [p] -> failwith "Liste à un seul élément"
  | p1::p2::[] -> [p1;p2]
  | (c1, s1, i1)::(c2, s2, i2)::(c3, s3, i3)::rl ->
     if (i1 <= i2 && i1 <= i3) then
       (chameau ((c2, s2, i2)::(c3, s3, i3)::rl))
     else if (i2 <= i1 && i2 <= i3) then
       (chameau ((c1, s1, i1)::(c3, s3, i3)::rl))
     else (chameau ((c1, s1, i1)::(c2, s2, i2)::rl))
;;

chameau inventaire;;                                           (* [pON8; pMR21] *)
chameau ((Objet, Robuste, 666)::pPF1::pCF3::pON8::pMR21::[]);; (* [pMR21; (Objet, Robuste, 666)] *)

(* 2.2. CHEZ TARDY *)

(* Exercice 25. Types *)

type produit = MP3 | Photo | Camera | Telephone | PC;;
type marque = Alpel | Syno | Massung | Liphisp;;
type prix = int;;
type stock = int;;
type article = produit * marque * prix * stock;;

let articles_egaux : article -> article -> bool =
  fun (prod1, marq1, prix1, stock1) ->
  fun (prod2, marq2, prix2, stock2) ->
  (prod1 == prod2 && marq1 == marq2 && prix1 == prix2)

(* Exercice 26. En stock *)

let rec est_en_stock : produit -> marque -> prix -> article list -> bool =
  fun prod ->
  fun marq ->
  fun prix ->
  fun l ->
  match l with
  | [] -> false
  | (prod2, marq2, prix2, stock2)::rl ->
     if (prod == prod2 && marq == marq2 && prix == prix2)
     then (stock2 > 0)
     else (est_en_stock prod marq prix rl)
;;

let a1 : article = (MP3, Alpel, 30, 1);;
let a2 : article = (Photo, Syno, 1000, 2);;
let a3 : article = (Telephone, Liphisp, 500, 3);;
let a4 : article = (MP3, Alpel, 40, 3);;
let inventaire : article list = [a1; a2; a3];;

est_en_stock MP3 Alpel 30 inventaire;;          (* false *)
est_en_stock Photo Syno 100 inventaire;;        (* false *)
est_en_stock Photo Syno 1000 inventaire;;       (* true *)
est_en_stock Telephone Liphisp 500 inventaire;; (* true *)

(* Exercice 27. Ajoute article *)

let rec ajoute_article : article -> article list -> article list =
  fun (prod, marq, prix, stock) ->
  fun l ->
  match l with
  | [] -> [prod, marq, prix, stock]
  | (prod2, marq2, prix2, stock2)::rl ->
     if (articles_egaux (prod, marq, prix, stock) (prod2, marq2, prix2, stock2)) then
       (prod, marq, prix, stock + stock2)::rl
     else (prod2, marq2, prix2, stock2)::(ajoute_article (prod, marq, prix, stock) rl)
;;

ajoute_article a1 inventaire;; (* [(MP3, Alpel, 30, 2);a2;a3] *)
ajoute_article a4 inventaire;; (* [a1;a2;a3;a4] *)

(* Exercice 28. Enlève article *)

let rec enleve_article : article -> article list -> article list =
  fun (prod, marq, prix, stock) ->
  fun l ->
  match l with
  | [] -> []
  | (prod2, marq2, prix2, stock2)::rl ->
     if (articles_egaux (prod, marq, prix, stock) (prod2, marq2, prix2, stock2)) then
       if (stock2 - stock <= 0) then rl
       else (prod, marq, prix, stock2 - stock)::rl
     else (prod2, marq2, prix2, stock2)::(enleve_article (prod, marq, prix, stock) rl)
;;

enleve_article a2 inventaire;;                           (* [a1;a3] *)
enleve_article (Telephone, Liphisp, 500, 1) inventaire;; (* [a1;(Telephone, Liphisp, 500, 2);a3] *)

(* 2.3. AIDONS MARC : ALGORITHMES DE BASE *)

(* Exercice 29. Ces produits *)

let rec ces_produits : produit -> article list -> article list =
  fun prod1 ->
  fun l ->
  match l with
  | [] -> []
  | (prod, marq, prix, stock)::rl when (prod1 == prod) ->
     (prod, marq, prix, stock)::(ces_produits prod1 rl)
  | a::rl -> ces_produits prod1 rl
;;

ces_produits MP3 [a1; a2; a3; a4];; (* [a1;a4] *)
ces_produits Photo inventaire;;     (* [a2] *)
ces_produits Telephone inventaire;; (* [a3] *)
ces_produits Camera inventaire;;    (* [] *)

(* Exercice 30. Le choix le plus courant *)

let rec deuxieme_moins_cher_rec : article list -> article =
  fun l ->
  match l with
  | [] -> failwith "Liste vide"
  | [a] -> failwith "Liste a un seul element"
  | (prod1, marq1, prix1, stock1)::(prod2, marq2, prix2, stock2)::[] ->
     if (prix1 >= prix2) then (prod1, marq1, prix1, stock1)
     else (prod2, marq2, prix2, stock2)
  |  (prod1, marq1, prix1, stock1)::(prod2, marq2, prix2, stock2)::(prod3, marq3, prix3, stock3)::rl ->
     if (prix1 >= prix2 && prix1 >= prix3) then
       (deuxieme_moins_cher_rec ((prod2, marq2, prix2, stock2)::(prod3, marq3, prix3, stock3)::rl))
     else if (prix2 >= prix1 && prix2 >= prix3) then
       (deuxieme_moins_cher_rec ((prod1, marq1, prix1, stock1)::(prod3, marq3, prix3, stock3)::rl))
     else (deuxieme_moins_cher_rec ((prod1, marq1, prix1, stock1)::(prod2, marq2, prix2, stock2)::rl))
;;

let rec deuxieme_moins_cher : produit -> article list -> article =
  fun prod ->
  fun l ->
  deuxieme_moins_cher_rec (ces_produits prod l)
;;

let pc1 : article = (PC, Alpel, 1, 1);;
let pc2 : article = (PC, Syno, 2, 1);;
let pc3 : article = (PC, Liphisp, 3, 1);;
let pc4 : article = (PC, Alpel, 4, 1);;

deuxieme_moins_cher PC [pc1; pc2; pc3; pc4];; (* pc2 *)
deuxieme_moins_cher PC [pc4; pc2; pc1; pc3];; (* pc2 *)
deuxieme_moins_cher PC [a1; pc1; pc2; a2];;   (* pc2 *)

(* Exercice 31. Budget *)

let rec budget : int -> int -> article list -> article list =
  fun bmin ->
  fun bmax ->
  fun l ->
  match l with
  | [] -> []
  | (prod, marq, prix, stock)::rl ->
     if (prix >= bmin && prix <= bmax) then
       (prod, marq, prix, stock)::(budget bmin bmax rl)
     else (budget bmin bmax rl)
;;

let pcs : article list = [pc1; pc2; pc3; pc4];;

budget (-1) 5 pcs;; (* pcs *)
budget 2 3 pcs;;  (* [pc2; pc3] *)
budget 5 6 pcs;;  (* [] *)

(* Exercice 32. Achète *)

let rec achete : produit -> marque -> prix -> article list -> article list =
  fun aprod ->
  fun amarq ->
  fun aprix ->
  fun l ->
  match l with
  | [] -> failwith "Article introuvable"
  | (prod1, marq1, prix1, stock1)::rl
       when (prod1 == aprod && marq1 == amarq && prix1 == aprix) ->
     if (stock1 - 1 < 0) then failwith "Article plus en stock"
     else if (stock1 - 1 > 0) then (prod1, marq1, prix1, stock1 - 1)::rl
     else rl
  | (prod1, marq1, prix1, stock1)::rl ->
     (prod1, marq1, prix1, stock1)::(achete aprod amarq aprix rl)
;;

(*
let a1 : article = (MP3, Alpel, 30, 1);;
let a2 : article = (Photo, Syno, 1000, 2);;
let a3 : article = (Telephone, Liphisp, 500, 3);;
let a4 : article = (MP3, Alpel, 40, 3);;
 *)

let inventaire : article list = [a1; a2; a3; a4];;

achete MP3 Alpel 30 inventaire;;          (* [a2; a3; a4] *)
achete Photo Syno 1000 inventaire;;       (* [a1; (Photo, Syno, 1000, 1); a3; a4] *)
achete Telephone Liphisp 500 inventaire;; (* [a1; a2; (Telephone, Liphisp, 500, 2); a4] *)
achete MP3 Alpel 40 inventaire;;          (* [a1; a2; a3; (MP3, Alpel, 40, 2)] *)

(* Exercice 33. Commande *)

let rec commande : article list -> article list =
  fun l ->
  match l with
  | [] -> []
  | (prod, marq, prix, stock)::rl when (stock == 0) ->
     (prod, marq, prix, stock)::(commande rl)
  | a::rl -> (commande rl)
;;

commande [(Photo, Alpel, 40, 0); (Photo, Alpel, 50, 0); (Photo, Alpel, 60, 1)];;
   (* [(Photo, Alpel, 40, 0); (Photo, Alpel, 50, 0)] *)
commande [(Photo, Alpel, 40, 1); (Photo, Alpel, 50, 2); (Photo, Alpel, 60, 3)];;
   (* [] *)
commande [(Photo, Alpel, 40, 0)];;
   (* [(Photo, Alpel, 40, 0)] *)

(* 2.4. TRI PAR SÉLECTION *)

(* Exercice 34. Trouve minimum *)

let rec trouve_min_rec : article list -> article =
  fun l ->
  match l with
  | [] -> failwith "Liste vide"
  | [a] -> a
  | (prod1, marq1, prix1, stock1)::(prod2, marq2, prix2, stock2)::rl ->
     if (prix1 < prix2)
     then (trouve_min_rec ((prod1, marq1, prix1, stock1)::rl))
     else (trouve_min_rec ((prod2, marq2, prix2, stock2)::rl))
;;

let trouve_min : article list -> article * article list =
  fun l ->
  let lmin : article = (trouve_min_rec l) in
  (lmin, (enleve_article lmin l))
;;

(*
let a1 : article = (MP3, Alpel, 30, 1);;
let a2 : article = (Photo, Syno, 1000, 2);;
let a3 : article = (Telephone, Liphisp, 500, 3);;
let a4 : article = (MP3, Alpel, 40, 3);;
 *)

trouve_min inventaire;;   (* a1 *)
trouve_min [a2; a4; a3];; (* a4 *)

(* Exercice 35. Tri par sélection *)

let rec tri_selection : article list -> article list =
  fun l ->
  match l with
  | [] -> []
  | l ->
     let (lmin, rl) : (article * article list) = (trouve_min l) in
     lmin::(tri_selection rl)
;;

tri_selection inventaire;;       (* [a1; a4; a3; a2] *)
tri_selection [a2; a3; a4; a1];; (* [a1; a4; a3; a2] *)
