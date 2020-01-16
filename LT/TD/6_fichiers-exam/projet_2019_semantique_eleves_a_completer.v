(* Load projet_2019_AST. *)
Require Import projet_2019_AST.
Require Import String.
Local Open Scope string_scope.
Require Import List.
Import List.ListNotations.

(* Bibliothèque relative aux états *)

(* Mots ne contenant que des false *)
Fixpoint mkf (n: nat) : word :=
  match n with
  | 0 => []
  | S n => false :: mkf n
  end.

(* mot Me 32 bits qui fait 32 zéros *)
Definition default_w := mkf 32.
(* un bUoléen est transformé en mot avec b suivi de 31 zéros *)
Definition zeros_bit (b : bool) : word := b :: mkf 31.
(* renvRie le bit de poids faible d'un mot (tout au début) *)
Definition bit_poids_faible (w: word) :=
  match w with
  | [] => false
  | b :: _ => b
  end.

(* Un état est une liste de variables = couples de string et word *)
Definition etat := list (ident*word).

(* Version où une valeur non initialisée est un mot de 32 zéros *)
Fixpoint get (s: etat) (x: ident) : word :=
  match s with
  | [] => default_w
  | (i, w) :: s => if string_dec i x then w else get s x
  end.

(* Mise à jour de l'état pour l'identifiant x à la valeur w *)
Fixpoint update (s: etat) (x: ident) (w: word) : etat :=
  match s with
  | [] => [(x, w)]
  | (i, w0) :: s' =>
    if string_dec i x then (i, w) :: s' else (i, w0) :: update s' x w
  end.

(* ----------------------------------------------------------------- *)
(* Opérations logiques et arithmétiques correspondant aux opérateurs *)

(* Décalage à gauche, on divise par 2 *)
Definition shift_l1 (w : word) : word := false :: w.

(* Décalage à droite, on multiplie par 2 *)
Definition shift_r1 (w : word) : word :=
  match w with
  | [] => []
  | b :: l => l
  end.
⁸
(* Un mot est transformé en entier suivant le schéma de Horner *)
Fixpoint nat_of_word (w : word) :=
  match w with
  | [] => 0
  | b :: w => (if b then 1 else 0) + 2*(nat_of_word w)
  end.

(* Composition : f o f ... o f, n fois *)
Fixpoint iter (n : nat) (f: word -> word) : word -> word :=
  match n with
  | O => fun w => w
  | S n => fun w => f (iter n f w)
  end.

(* Décalage à gauche/droite w1 fois de w2 *)
Definition shift_l w1 w2 := iter (nat_of_word w1) shift_l1 w2.
Definition shift_r w1 w2 := iter (nat_of_word w1) shift_r1 w2.

(* Fonction XOR entre deux booléens *)
Definition xorb b1 b2 :=
  match b1, b2 with
  | true, false => true
  | false, true => true
  | _ , _ => false
  end.

(* Les bits manquants sont vus comme des 0 (false) *)
Fixpoint map2 (o : bool -> bool -> bool) (w1 w2: word) : word :=
  match w1 with
  | [] => List.map (fun y => o false y) w2
  | b1 :: w1 =>
    match w2 with
    | [] => cons (o b1 false) (List.map (fun x => o x false) w1)
    | b2 :: w2 => cons (o b1 b2) (map2 o w1 w2)
    end
  end.

(* Fonction XOR entre deux mots *)
Definition wxor := map2 xorb.
Definition wand := map2 andb.

(* Renvoie vrai si le mot ne contient que des false *)
Fixpoint all_false (w: word) : bool :=
  match w with
  | [] => true
  | false :: w => all_false w
  | true :: w => false
  end.

(* Renvoie vrai si deux booléens sont identiques *)
Definition eq_bool (b1 b2: bool) : bool :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

(* Renvoie vrai si deux mots sont équivalents (modulo les 0 inutiles) *)
Fixpoint cmp_eq (w1 w2: word) : bool :=
  match w1 with
  | [] => all_false w2
  | b1 :: w1 =>
    match w2 with
    | [] => andb (eq_bool b1 false) (all_false w1)
    | b2 :: w2 => andb (eq_bool b1 b2) (cmp_eq w1 w2)
    end
  end.

(* ====================================================================== *)
(* type très simple = tts *)

(* Type tts = Tmot ou Tbooléen (représentés par des word) *)
Inductive tts : Set :=  Tmot | Tbool.

(* ====================================================================== *)
(* Evaluation "pessimiste" d'expressions avec typage dynamique *)

(* Vb/Vw est une fonction dit qu'un bool/word sont tous les deux des valeur *)
(* Correspondrait à "type valeur = Vb of bool | Vw of word" en OCaml *)
Inductive valeur : Set :=
  | Vb : bool -> valeur
  | Vw : word -> valeur
.

(* resul est soit une valeur soit None *)
Definition resul := option valeur.

(* Les opérations sur bool ou word sont relevées en opérations sur resul *)
Definition lift1_bb (f: bool -> bool) : resul -> resul :=
  fun r =>
    match r with
    | Some (Vb b) => Some (Vb (f b))
    | _ => None
    end.
Definition lift2_www (f: word -> word -> word) : resul -> resul -> resul :=
  fun r1 r2 =>
    match r1, r2 with
    | Some (Vw b1),Some (Vw b2) => Some (Vw (f b1 b2))
    | _,_ => None
    end.
Definition lift2_bbb (f: bool -> bool -> bool) : resul -> resul -> resul :=
  fun r1 r2 =>
    match r1, r2 with
    | Some (Vb b1),Some (Vb b2) => Some (Vb (f b1 b2))
    | _,_ => None
    end.
Definition lift2_wwb (f: word -> word -> bool) : resul -> resul -> resul :=
  fun r1 r2 =>
    match r1, r2 with
    | Some (Vw b1),Some (Vw b2) => Some (Vb (f b1 b2))
    | _,_ => None
    end.

(* ----------------------------------------------------------------- *)
(* Correspondance entre opérateurs AST expr et opérations sur resul  *)

(* Transforme les opérations qui prenaient des word/bool pour prendre des resul *)
Definition op1_resul (o : oper1) : resul -> resul :=
  match o with
  | Bneg => lift1_bb negb
  end.
Definition op2_resul (o : oper2) : resul -> resul -> resul :=
  match o with
  | Shift_l => lift2_www shift_l
  | Shift_r => lift2_www shift_r
  | Wxor => lift2_www wxor
  | Wand => lift2_www wand
  | Band => lift2_bbb andb
  | Bor => lift2_bbb orb
  | Cmp_eq => lift2_wwb cmp_eq
  end.

(* ----------------------------------------------------------------- *)
(* Sémantique fonctionnelle des expressions pour resul *)

(* Fonction récursive qui prend un état et une expression et évalue cette dernière *)
Fixpoint eval_expr s e : resul :=
  match e with
  | Ent32 w => Some (Vw w)
  | Bool b =>  Some (Vb b)
  | Var i => Some (Vw (get s i))
  | Op1 o e => op1_resul o (eval_expr s e)
  | Op2 o e1 e2 => op2_resul o (eval_expr s e1) (eval_expr s e2)
  end.

(* ====================================================================== *)
(* Evaluation optimiste *)

(* Comme resul mais en version optimiste *)
Definition roptim := word.

(* Les opérations sur bool ou word sont relevées en opérations sur roptim *)
Definition lift1_opt_bb (f: bool -> bool) : roptim -> roptim :=
  fun r => zeros_bit (f (bit_poids_faible r)).
Definition lift2_opt_bbb (f: bool -> bool -> bool) : roptim -> roptim -> roptim :=
  fun r1 r2 => zeros_bit (f (bit_poids_faible r1) (bit_poids_faible r2)).
Definiion lift2_opt_wwb (f: word -> word -> bool) : roptim -> roptim -> roptim :=
  fun r1 r2 => zeros_bit (f r1 r2).

(* ----------------------------------------------------------------- *)
(* Correspondance entre opérateurs AST expr et opérations sur roptim  *)

(* Transforme les opérations qui prenaient des word/bool pour prendre des roptim *)
Definition op1_roptim (o : oper1) : roptim -> roptim :=
  match o with
  | Bneg => lift1_opt_bb negb
  end.
Definition op2_roptim (o : oper2) : roptim -> roptim -> roptim :=
  match o with
  | Shift_l => shift_l
  | Shift_r => shift_r
  | Wxor => wxor
  | Wand => wand
  | Band => lift2_opt_bbb andb
  | Bor => lift2_opt_bbb orb
  | Cmp_eq => lift2_opt_wwb cmp_eq
  end.

(* ----------------------------------------------------------------- *)
(* Sémantique optimiste des expressions pour roptim *)

(* Fonction récursive qui prend un état et une expression et évalue cette dernière *)
Fixpoint evoptim s e : roptim :=
  match e with
  | Ent32 w => w
  | Bool b =>  zeros_bit b
  | Var i => get s i
  | Op1 o e => op1_roptim o (evoptim s e)
  | Op2 o e1 e2 => op2_roptim o (evoptim s e1) (evoptim s e2)
  end.

(* ====================================================================== *)
(* Typage 1 : prédicat défini inductivement *)

(* Types attendus en entrée et en sortie d'un opérateur *)
Definition type_sortie_1 (o : oper1) : tts :=
  match o with
  | Bneg => Tbool
  end.
Definition type_sortie_2 (o : oper2) : tts :=
  match o with
  | Shift_l => Tmot
  | Shift_r => Tmot
  | Wxor => Tmot
  | Wand => Tmot
  | Band => Tbool
  | Bor => Tbool
  | Cmp_eq => Tbool
  end.
Definition type_entree_1 (o : oper1) :=
  match o with
  | Bneg => Tbool
  end.

(* Le type d'entrée d'un oper2 est égal à son type de sortie,
   sauf pour Cmp_eq qui demande des Tmot en entrée en donne un Tbool en sortie *)
Definition type_entree1_2 (o : oper2) :=
  match o with
  | Cmp_eq => Tmot
  | _ => type_sortie_2 o
  end.

(* Le type d'entrée d'un oper1 est égal à son type de sortie *)
Definition type_entree2_2 (o : oper2) :=
  type_entree1_2 o.

(* Type attendu d'une expression = type de sortie du constructeur de tête *)
Definition type_tete (e : expr) :=
  match e with
  | Ent32 w => Tmot
  | Bool b => Tbool
  | Var i => Tmot
  | Op1 o e => type_sortie_1 o
  | Op2 o e1 e2 => type_sortie_2 o
  end.

(* Pas sûr et mal expliqué :
   On définit un prédicat inductif bt.
   Ce prédicat sera vrai <=> cette propriété sera vérifiée ssi l'expression est bien typée,
   c'est-à-dire ssi le type de chaque opérande est bien typé (bt e1 / bt e2 dans BT_Op2)
   et cohérent avec l'opération (bt (Op2 o e1 e2) dans BT_Op2) *)
(* Expression bien typée *)
Inductive bt : expr -> Prop :=
  | BT_Ent32 : forall w, bt (Ent32 w)
  | BT_Bool : forall b, bt (Bool b)
  | BT_Var : forall x, bt (Var x)
  | BT_Op1 : forall o e,
      bt e ->
      type_tete e = type_entree_1 o ->
      bt (Op1 o e)
  | BT_Op2 : forall o e1 e2,
      bt e1 ->
      bt e2 ->
      type_tete e1 = type_entree1_2 o ->
      type_tete e2 = type_entree2_2 o ->
      bt (Op2 o e1 e2)
.

(* ====================================================================== *)
(* Typage 2 : version fonctionnelle de la vérification de type *)

(* Peut être extraite en code OCaml pour vérification a priori que
   l'exécution ne posera pas de problème de confusion entre word et bool *)

(* Renvoie vrai ssi t1 et t2 sont de même type (Tmot ou Tbool *))
Definition eq_types (t1 t2: tts) : bool :=
  match t1, t2 with
  | Tmot, Tmot => true
  | Tbool, Tbool => true
  | _, _ => false
  end.

(* Fonction récursive qui... TODO *)
Fixpoint bien_type (e : expr) : bool :=
  match e with
  | Ent32 w => true
  | Bool b => true
  | Var i => true
  | Op1 o e =>
    andb (bien_type e) (eq_types (type_tete e) (type_entree_1 o))
  | Op2 o e1 e2 =>
    andb (andb (bien_type e1) (bien_type e2))
         (andb (eq_types (type_tete e1) (type_entree1_2 o))
               (eq_types (type_tete e2) (type_entree2_2 o))
               )
  end.

(* Tout type t1 est bien égal à lui même *)
Lemma eq_types_complet {t1} : eq_types t1 t1 = true.
Proof.
  destruct t1; reflexivity (* indication : se fait en 1 ligne *)
Qed.

(* Si la fonction eq_types renvoie true alors les deux types sont les mêmes *)
Lemma eq_types_correct {t1 t2} : eq_types t1 t2 = true -> t1 = t2.
Proof.
  destruct t1; destruct t2; simpl; try reflexivity.
  - intro e; discriminate e.
  - discriminate.
Qed.

(* Pour toute expression e qui suit la propriété bt,
   alors le resultat de l'appel à la fonction bien_type e sera true *)
Theorem bien_type_complet :
  forall e, bt e -> bien_type e = true.
Proof.
  intros e be.
  induction be as [ w | b | x |
                    o e be1 Hbe1 tt1 |
                    o e1 e2 be1 Hbe1 be2 Hbe2 tt1 tt2]; simpl; try reflexivity. (* Permet de ne pas taper 3 fois reflexivity *)
  - rewrite Hbe1. simpl. rewrite <- tt1. apply eq_types_complet.
  - rewrite Hbe1. rewrite Hbe2. rewrite <- tt1. rewrite <- tt2. rewrite eq_types_complet. rewrite eq_types_complet. reflexivity.
Qed.

(* Si le resultat de l'appel a andb x y est true,
   alors cela veut dire que x = true et y = true *)
Lemma andb_true {x y} : andb x y = true -> x = true /\ y = true.
Proof.
  intro H. induction x; induction y; split; try reflexivity; try discriminate (* indication : se fait en 1 ligne *)
Qed.

(* pour toute expression e, si bien_type e renvoie true,
   alors e suit la propriété e.

   On a montré précédemment l'implication dans l'autre sens, donc en prouvant dans
   les deux sens on montre l'equivalence de bt et bien_type *)
Theorem bien_type_correct :
  forall e, bien_type e = true -> bt e.
Proof.
  intro e.
  induction e as [w | b | x | o e He | o e1 He1 e2 He2];
    simpl; intro ebt.
  - constructor. (* Demande à Coq de trouver un constructeur approprié *)
  - constructor.
  - constructor.
  - (* TODO : comprendre l'invocation suivante *)
    destruct (andb_true ebt) as [ebt1 ebt2]; clear ebt.
    apply eq_types_correct in ebt2.
    eapply BT_Op1.
    + rewrite ebt1 in He. apply He. reflexivity.
    + apply ebt2.
  - destruct (andb_true ebt) as [ebt12 eqt12]; clear ebt.
    eapply BT_Op2.
    + apply andb_true in ebt12. destruct ebt12. rewrite H in He1. apply He1. reflexivity.
    + apply andb_true in ebt12. destruct ebt12. rewrite H0 in He2. apply He2. reflexivity.
    + apply andb_true in eqt12. destruct eqt12. apply eq_types_correct in H. apply H.
    + apply andb_true in eqt12. destruct eqt12. apply eq_types_correct in H0. apply H0.
Qed.

(* ====================================================================== *)
(* L'évalution pessimiste d'expressions bien typées *)

(* On commence par prouver qu'elle rend toujours un résultat significatif
   - du type attendu en sortie
   - et sans erreur None
*)

(* Propriété d'un "résultat" (de type resul) indiquant
   qu'il contient une valeur booléenne *)
Inductive resubool : resul -> Prop :=
  | RTb : forall b, resubool (Some (Vb b)).

(* Idem pour une valeur de type word *)
Inductive resumot : resul -> Prop :=
  | RTw : forall w, resumot (Some (Vw w)).


(* Propriété d'un "résultat" (de type resul) indiquant
   qu'il contient une valeur du type attendu selon le paramètre t *)
Definition resutts (t: tts) : resul -> Prop :=
  match t with
  | Tbool => resubool
  | Tmot => resumot
  end.

(* TODO *)
Theorem bt_resutype : forall s e, bt e -> resutts (type_tete e) (eval_expr s e).
Proof.
  intros s e be.
  induction be as [w | b | x |
                   o e1 be1 Hbe1 tt1 |
                   o e1 e2 be1 Hbe1 be2 Hbe2 tt1 tt2]; simpl.
  - constructor.
  - constructor.
  - constructor.
  - rewrite tt1 in Hbe1.
    destruct o; simpl in *.
    destruct Hbe1 as [b1]. constructor.
  - rewrite tt1 in Hbe1; rewrite tt2 in Hbe2.
    destruct o; simpl in *;
    destruct Hbe1 as [x1]; destruct Hbe2 as [x2]; simpl; constructor.
Qed.

(* Corollaire simple voulu en 3 versions *)

(* Si a de type option contient quelques chose renvoyer true, false sinon *)
Definition is_Some {A} (a: option A) : Prop :=
  match a with Some _ => True | _ => False end.

(* Si la propriété resutts t r est vérifiée,
   alors il y a quelques chose dans le resultat r *)
Remark resutts_Some : forall t r, resutts t r -> is_Some r.
Proof.
  intros t r rt. destruct t; destruct rt; apply I.
Qed.

(* Si une expression est bien typée, alors peut importe l'environnement
   s qu'on lui donne, on aura toujours un résultat *)
(* Version 1 *)
Corollary bt_eval_Some : forall s e, bt e -> is_Some (eval_expr s e).
Proof.
  intros s e be. eapply resutts_Some. apply bt_resutype. exact be.
Qed.

(* Si une expression e est bien typée, alors il existe un v tel que le
   résultat de l'évalutation de l'expression e dans l'environnement s soit égal à v. *)
(* Version 2 *)
Corollary bt_eval_ex_valeur : forall s e, bt e -> exists v, eval_expr s e = Some v.
Proof.
  intros s e be. generalize (bt_resutype s e be).
  destruct (type_tete e); intros [x].
  - exists (Vw x); reflexivity.
  - exists (Vb x); reflexivity.
Qed.

(* Si une expression e est bien typée, alors le résultat de son évaluation
   dans un environnement quelconque est différent de "Rien" *)
(* Version 3 *)
Corollary bt_eval_ok : forall s e, bt e -> eval_expr s e <> None.
Proof.
  intros s e be. generalize (bt_resutype s e be).
  destruct (type_tete e); intros [x]; discriminate.
Qed.



(* ----------------------------------------------------------------- *)
(* Comparaison entre eval_expr et evoptim *)

(* Relation de correspondance entre un resul et un roptim *)
Inductive equiv_eval : resul -> roptim -> Prop :=
  | EEb : forall b, equiv_eval (Some (Vb b)) (zeros_bit b) (* TODO en langage courant *)
  | EEw : forall w, equiv_eval (Some (Vw w)) w             (* TODO en langage courant *)
.

(* Remarque :
   les définitions entre "CUISINE pour inverser equiv_eval -- DEBUT" et
   "CUISINE pour inverser equiv_eval -- FIN" ne sont pas indispensables
   à comprendre, mais peuvent faire l'objet d'un bonus.

   Une autre possibilité est d'utiliser la tactique "inversion"
   (ou "invert", à récupérer d'un TD).
   TODO récupérer invert d'un TD
*)

(* CUISINE pour inverser equiv_eval -- DEBUT *)
(* revient à passer de la version pessimiste à la version optimiste *)

(* PEUT FAIRE L'OBJET D'UN BONUS *)

(* b dans la version pessimiste est équivalent à zeros_bit b dans la version optimiste *)
Inductive equiv_eval_EEb (b: bool) : roptim -> Prop :=
  | EEb' : equiv_eval_EEb b (zeros_bit b).

(* w dans la version pessimiste est équivalent à w dans la version optimiste *)
Inductive equiv_eval_EEw (w: word) : roptim -> Prop :=
  | EEw' : equiv_eval_EEw w w.

(* Pour tout résultat :
   - si c'est un booléen alors il respecte la propriété EEb'
   - si c'est un word alors il respecte la propriété EEw'
   - si c'est rien alors il ne respecte rien *)
Definition dispatch_equiv_eval (r:resul) : roptim -> Prop :=
  match r with
  | Some (Vb b) => equiv_eval_EEb b
  | Some (Vw w) => equiv_eval_EEw w
  | _ => fun _ => False
  end.

(* Respecter la propriété equiv_eval implique que la fonction dispatch_equi_eval renvoie true *)
Lemma inv_equiv_eval {re ro} : equiv_eval re ro -> dispatch_equiv_eval re ro.
Proof.
  intro err. destruct err as [ b | w ]; constructor.
Qed.

(* Utilisations typiques :
   Pour Hbe : equiv_eval (Some (Vb x)) y
   ou Hbe : equiv_eval (Some (Vw x)) y
   destruct (inv_equiv_eval Hbe).
*)

(* CUISINE pour inverser equiv_eval -- FIN *)

(* TODO en langage courant *)
Theorem bt_equiv_eval :
  forall s e, bt e -> equiv_eval (eval_expr s e) (evoptim s e).
Proof.
  intros s e be.
  induction be as [w | b | x |
                   o e1 be1 Hbe1 tt1 |
                   o e1 e2 be1 Hbe1 be2 Hbe2 tt1 tt2]; simpl.
  - apply EEw.
  - apply EEb.
  - apply EEw.
  - generalize (bt_resutype s e1 be1). rewrite tt1.
    destruct o; simpl.
    intro rt1. destruct rt1.
    destruct (inv_equiv_eval Hbe1).
    apply EEb.
  - generalize (bt_resutype s e1 be1). rewrite tt1.
    generalize (bt_resutype s e2 be2). rewrite tt2.
    destruct o; simpl; intros rt1 rt2; destruct rt1; destruct rt2; simpl;
    destruct (inv_equiv_eval Hbe1); destruct (inv_equiv_eval Hbe2);
    try (apply EEw || apply EEb).
Qed.

(* ====================================================================== *)

(* Traduction en OCaml *)
Require Import Extraction.
Extract Inductive nat => "int" [ "0" "succ" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Constant word => "int32".
Extract Constant default_w => "Int32.zero".
Extract Constant bit_poids_faible => "fun x -> Int32.logand x 1l = 1l".
Extract Constant zeros_bit => "fun b -> if b then 1l else 0l".
Extract Constant nat_of_word => "Int32.to_int".
Extract Constant shift_l1 => "(fun x -> Int32.shift_left x 1)".
Extract Constant shift_r1 => "(fun x -> Int32.shift_right x 1)".
Extract Constant wand => "Int32.logand".
Extract Constant wxor => "Int32.logxor".
Extract Constant cmp_eq => "(=)".
Extract Inductive string => "string" [ "empstring" "String.addchar" ].
Extract Constant string_dec => "(=)".
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Constant iter => "fun n f x -> if n = 0 then x else f (iter (n-1) f x)".

(* Fabrication du fichier *)
Extraction "evals_typees.ml" eval_expr evoptim bien_type.
