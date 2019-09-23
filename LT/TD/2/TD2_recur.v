(** INITIATION A LΑ RÉCURRENCE EN COQ *)


(** * Arbres binaires *)

Inductive coulfeu : Set :=
  | vert : coulfeu
  | orange : coulfeu
  | rouge : coulfeu
.

Check coulfeu.

Inductive arbin : Set :=
  | V : coulfeu -> arbin
  | N : arbin -> arbin -> arbin.

Check (N (V vert) (V orange)).
Definition monarbin :=
  (N (V vert) (N (V orange) (V rouge))).

(**
Pour définir une fonction récursive (l'équivalent de let rec
en OCaml) on utilise le mot clé Fixpoint.
 *)

Fixpoint renva a : arbin :=
  match a with
  | V c => V c
  | N g d => N (renva d) (renva g)
  end.

Check (renva monarbin).
Eval compute in (renva monarbin).

(* Prouvez que renverser deux fois un arbre rend le même arbre *)
Theorem renva_renva : forall a, renva (renva a) = a.
Proof.
  (* preuve par récurrence *)
  apply arbin_ind.
  - (* cas de base : V *)
    intro c.
    compute.
    trivial.
  - (* cas Noeud : N *)
    intros g hrec_g d hrec_d. (* g et d forall *)
    simpl. (* on ne fait pas compute sinon ça serait infini *)
    Check f_equal2.
    apply f_equal2.
    + apply hrec_g.
    + apply hrec_d.
    (** (* autre possibilité *)
    rewrite hrec_g.
    rewrite hrec_d.
    trivial.
     *)
Qed.

(** 
Attention : il faut être capable de rédiger sous forme de texte usuel 
le raisonnement formalisé ci-dessus en Coq, soit avant, soit a posteriori.
*)

(*
Le reste du TD est destiné à exprimer en Coq la preuve par récurrence
sur les expressions arithmétiques vue au TD1.
Auparavant on a besoin de 

*)


(** * Conjonctions et disjonctions de propositions *)

(** Exercices/exemples triviaux (vus en cours) *)

(**
Rappel des tectiques :
- intro
- apply
- le couteau suisse : destruct nom_hypothèse as [... | ... ]
- split
- left, right
*)

Section prop.

  Variables P Q : Prop.
  Lemma conj_com :  P /\ Q -> Q /\ P.
  Proof.
    intro H.
    destruct H as [hP hQ].
    Locate "/\".
    Print and.
    Check conj.
    (* apply conj;[apply hQ|apply hP]. *)
    apply conj.
    - apply hQ. (* assumption. trivial. *)
    - apply hP.
  Qed.

Lemma disj_com : P \/ Q -> Q \/ P .
  Proof.
    Locate "\/".
    intro h.
    destruct h as [hP|hQ].
    - right.
      apply hP.
    - left.
      apply hQ.
  Qed.

End prop.


(** * Expressions arithmétiques *)

(** ** Définitions *)


(** On considère une variante simplifiée des expressions arithmétiques vues en cours/TD,
    ne comportant des opératuers que pour l'addition et la multiplication.
    On utilisera le type nat (entiers naturels de Coq) pour représenter les entiers
    et on nommera les différents constructeurs/opérateurs
    Ana (pour les naturels), Apl et Amu pour l'addition et la multiplication *)

Inductive Aexp : Set :=
| Ana: nat -> Aexp
| Apl: Aexp -> Aexp -> Aexp
| Amu: Aexp -> Aexp -> Aexp
.


(* Définir les expressions Aexp correspondant à
  - (1 + 2) * 3
  - (1 * 2) + 3
  - (((1 + (2*3)) * 5) + (3*4))
 *)

Definition exp_1 := (Amu (Apl (Ana 1) (Ana 2)) (Ana 3)).

Definition exp_2 := (Apl (Amu (Ana 1) (Ana 2)) (Ana 3)).

Definition exp_3 := (Apl (Amu (Apl (Ana 1) (Amu (Ana 2) (Ana 3))) (Ana 5)) (Amu (Ana 3) (Ana 4))).

(** Définir en Coq la fonction d'évaluation sémantique fonctionnelle Sf de Aexp
    en utilisant les operateurs arithmétiques de Coq sur le type nat : + *       *)

Fixpoint eval (a: Aexp) : nat :=
  match a with
    | Ana n => n
    | Apl e1 e2 => (eval e1) + (eval e2)
    | Amu e1 e2 => (eval e1) * (eval e2)
  end.

(** Evaluer avec Compute la sémantique de exp_1, exp_2 et exp_3 *)

Eval compute in (eval exp_1).
Eval compute in (eval exp_2).
Eval compute in (eval exp_3).

(** ** Expressions paires *)

(** On pose la définition suivante *)
Definition pair (n:nat):=
  exists p, n = 2*p.

(** Et on admet les propriétés suivantes *)
Lemma plus_pair : forall n1 n2, pair n1 -> pair n2 -> pair (n1 + n2).
Proof.
Admitted.
Lemma mult_pair_1 : forall n1 n2, pair n1 -> pair (n1 * n2).
Proof.
Admitted.
Lemma mult_pair_2 : forall n1 n2, pair n2 -> pair (n1 * n2).
Proof.
Admitted.

(** On peut définir des prédicats récursivement, par exemple celui
    qui indique qu'un entier x a des occurrences dans l'expression e *)

  
Fixpoint DansExp (x:nat) (e:Aexp) : Prop :=
  match e with
  | Ana n => x = n
  | Apl e1 e2 => DansExp x e1 \/ DansExp x e2
  | Amu e1 e2 => DansExp x e1 \/ DansExp x e2
  end.

Eval compute in (DansExp 42 exp_2).

(** Utilisation pour définir un prédicat qui nous intéresse *)
Definition TousPairs (e:Aexp) : Prop :=
  forall x, DansExp x e -> pair x.

(** Et voici l'exercice du TD1 *)
(** Pour le résoudre il est parfois utile d'effectuer un
    peu de calcul sur le but courant. 
    Les tactiques à essayer sont simpl, red et hnf,
    éventuellement unfold <nom_de_fonction> *)
Lemma TousPairs_eval : forall e, TousPairs e -> pair (eval e). 
Proof.
  intros exp.
  induction exp as [ n |                      (* cas Ana *)
                     e1 hrec_e1 e2 hrec_e2 |  (* cas Apl *)
                     e1 hrec_e1 e2 hrec_e2 ]. (* cas Amu *)
  - intro h.
    simpl.
    hnf in h.
    apply h.
    simpl.
    trivial.
  - intro h.
    simpl.
    apply plus_pair.
    + apply hrec_e1. (* premier sous cas addition *)
      hnf.
      hnf in h.
      intros x hx.
      apply h.
      hnf.
      left.
      apply hx.
    + admit.(* deuxième sous cas addition *)
  - intro h.
    (* à finir *)
    admit.
  (* unfold TousPairs. *)
Admitted.

(** ** Variante *)

(** Une autre définition possible de TousPairs, sans passer par DansExp est : *)
  
Fixpoint TousPairsConj (e:Aexp) : Prop :=
  match e with
  | Ana n => pair n
  | Apl e1 e2 => TousPairsConj e1 /\ TousPairsConj e2
  | Amu e1 e2 => TousPairsConj e1 /\ TousPairsConj e2
  end.

Lemma DansTousPairsConj_eval : forall e, TousPairsConj e -> pair (eval e). 
Proof.
Admitted.

(** * Exercices complémentaires *)


Lemma TousPairsConj_TousPairs :
  forall e, TousPairsConj e -> TousPairs e.
Proof.
Admitted.  

Lemma TousPairs_TousPairsConj :
  forall e, TousPairs e -> TousPairsConj e.
Proof.
Admitted.  




(** Décrire une propriété qui affirme que Apl est commutatif
    et la montrer par induction. On pourra utiliser la propriété
    suivante admise pour l'instant *)


Lemma plus_comm : forall n m : nat, n + m = m + n.
Proof. Admitted.

Theorem Apl_comm : forall (a1 a2:Aexp), (* Complétez ici *).
Proof.
  (* Complétez ici *)
Admitted.

(* La bibliothèque standard de Coq contient une définition des
   inégalités comme propositions, par exemple *)

Check 1 <= 2.

(* On admet le lemme suivant *)
Lemma leq_minus : forall n m, n <= m -> n - m = 0.
Proof.
Admitted.

(* Prouvez la propriété suivante *)
Theorem Amo_leq : forall (a1 a2 : Aexp), Sf a1 <= Sf a2 -> Sf (Amo a1 a2) = 0.
Proof.
  (* Complétez ici *)
Admitted.



(** ** Problème optionel : En provenance de PF *)

  (* Nombre de feuilles d'un arbre *)
Fixpoint nbf a : nat :=
  match a with
  | V _ => 1
  | N g d => nbf g + nbf d
  end.

(* Nombre de noeuds d'un arbre *)
Fixpoint nbc a : nat :=
  match a with
  | V _ => 0
  | N g d => nbc g + 1 + nbc d
  end.

(* On aura besoin du lemme suivant, admis pour le moment *)

Theorem plus_assoc : forall n m p : nat, n + (m + p) = n + m + p.
Proof. Admitted.

(* Prouver que la relation suivante entre le nombre de feuilles et le
   nombre de noeuds d'un arbre binaire *)

Theorem nbf_nbc : forall a, nbf a = nbc a + 1.
Proof.
  (* Complétez ici *)
Admitted.
