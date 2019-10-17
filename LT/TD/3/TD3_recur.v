(** INITIATION A LΑ RÉCURRENCE EN COQ, SUITE *)

(** Rappel : il faut être capable de rédiger sous forme de texte usuel
tout raisonnement formalisé en Coq, de préférence a priori, 
éventuellement a posteriori.
*)


(**
Rappel des tactiques qui vont servir :
- intro
- apply
- le couteau suisse : destruct nom_hypothèse as [... | ... ]
- split
- left, right
- simpl
- induction nom_hypothèse as [... | ... ] 
*)

(** 
On rappelle le type inductif des expressions arithmétiques constantes,
et sa sémantique fonctionnelle donnée par la fonction eval
 *)


Inductive Aexp : Set :=
| Ana : nat -> Aexp
| Apl : Aexp -> Aexp -> Aexp
| Amu : Aexp -> Aexp -> Aexp
| Amo : Aexp -> Aexp -> Aexp
.

Fixpoint eval (a: Aexp) : nat :=
  match a with
  | Ana n => n
  | Apl a1 a2 => eval a1 + eval a2
  | Amu a1 a2 => eval a1 * eval a2
  | Amo a1 a2 => eval a1 - eval a2
  end.


(** On pose la définition suivante, mais son contenu ne servira pas *)
Definition pair (n:nat):=
  exists p, n = 2*p.

(** On se reposera en effet uniquement sur ses propriétés, admises *)
Lemma plus_pair : forall n1 n2, pair n1 -> pair n2 -> pair (n1 + n2).
Proof.
Admitted.
Lemma mult_pair_1 : forall n1 n2, pair n1 -> pair (n1 * n2).
Proof.
Admitted.
Lemma mult_pair_2 : forall n1 n2, pair n2 -> pair (n1 * n2).
Proof.
Admitted.
Lemma moins_pair : forall n1 n2, pair n1 -> pair n2 -> pair (n1 - n2).
Proof.
Admitted.


(** On définit des prédicats récursivement, par exemple celui
    qui indique qu'un entier x a des occurrences dans l'expression e *)


Fixpoint DansExp (x:nat) (e:Aexp) : Prop :=
  match e with
  | Ana n => x = n
  | Apl e1 e2 => DansExp x e1 \/ DansExp x e2
  | Amu e1 e2 => DansExp x e1 \/ DansExp x e2
  | Amo e1 e2 => DansExp x e1 \/ DansExp x e2
  end.


(** Utilisation pour définir un prédicat qui nous intéresse *)
Definition TousPairs (e:Aexp) : Prop :=
  forall x, DansExp x e -> pair x.

(** Une autre définition possible de TousPairs, sans passer par DansExp : *)

Fixpoint TousPairsConj (e:Aexp) : Prop :=
  match e with
  | Ana n => pair n
  | Apl e1 e2 => TousPairsConj e1 /\ TousPairsConj e2
  | Amu e1 e2 => TousPairsConj e1 /\ TousPairsConj e2
  | Amo e1 e2 => TousPairsConj e1 /\ TousPairsConj e2
  end.

(** Démontrer les deux lemmes suivants -- 
    rappel : l'un a été fait lors du TD2 *)

Lemma TousPairs_eval : forall e, TousPairs e -> pair (eval e).
Proof.
  intros exp.
  induction exp as [ n |                      (* cas Ana *)
                     e1 hrec_e1 e2 hrec_e2 |  (* cas Apl *)
                     e1 hrec_e1 e2 hrec_e2 |  (* cas Amu *)
                     e1 hrec_e1 e2 hrec_e2 ]; (* cas Amo *)
            intro h ; simpl.
  - hnf in h.
    apply h.
    simpl.
    trivial.
  - apply plus_pair.
    + apply hrec_e1. (* premier sous cas addition *)
      hnf.
      hnf in h.
      intros x hx.
      apply h.
      hnf.
      left.
      apply hx.
    + apply hrec_e2. (* deuxième sous cas addition *)
      hnf.
      hnf in h.
      intros x hx.
      apply h.
      hnf.
      right.
      apply hx.
  - apply mult_pair_1.
    + apply hrec_e1. (* premier sous cas multiplication *)
      hnf.
      hnf in h.
      intros x hx.
      apply h.
      hnf.
      left.
      apply hx.
  - apply moins_pair.
    + apply hrec_e1. (* premier sous cas soustraction *)
      hnf.
      hnf in h.
      intros x hx.
      apply h.
      hnf.
      left.
      apply hx.
    + apply hrec_e2. (* deuxième sous cas soustraction *)
      hnf.
      hnf in h.
      intros x hx.
      apply h.
      hnf.
      right.
      apply hx.
Qed.

Lemma DansTousPairsConj_eval : forall e, TousPairsConj e -> pair (eval e).
Proof.
  intros e tpce.
  induction e as [ (* Ana *) n |
                   (* Apl *) epl1 hrec1 epl2 hrec2 |
                   (* Amu *) emu1 hrec1 emu2 hrec2 |
                   (* Amo *) emo1 hrec1 emo2 hrec2 ] ;
                 simpl in *.
  - apply tpce.
  - destruct tpce as [ tpce1 tpce2 ].
    apply plus_pair.
    + apply hrec1.
      apply tpce1.
    + apply hrec2.
      apply tpce2.
  - auto.
    destruct tpce as [ tpce1 tpce2 ].
    apply mult_pair_2.
    apply hrec2.
    apply tpce2.
  - destruct tpce as [ tpce1 tpce2 ].
    apply moins_pair.
    + apply hrec1.
      apply tpce1.
    + apply hrec2.
      apply tpce2.
Qed.

(** * Exercices complémentaires.
 Les élèves qui finissent rapidement les exercices précédents peuvent les faire
 d'emblée
 Les autres devront les faire à la maison.
*)


Lemma TousPairsConj_TousPairs :
  forall e, TousPairsConj e -> TousPairs e.
Proof.
Admitted.

Lemma TousPairs_TousPairsConj :
  forall e, TousPairs e -> TousPairsConj e.
Proof.
Admitted.


(** * Exercices sur apply *)


(** Décrire une propriété qui affirme que Apl est commutatif
    et la montrer par induction. On pourra utiliser la propriété
    suivante admise pour l'instant *)


Lemma plus_comm : forall n m : nat, n + m = m + n.
Proof.
Admitted.

(*
Theorem Apl_comm : forall (a1 a2:Aexp),
  Apl a1 a2 = Apl a2 a1.
--> pas vrai !
*)

Theorem Apl_comm : forall (a1 a2:Aexp),
  eval (Apl a1 a2) = eval (Apl a2 a1).
Proof.
  intros a1 a2.
  simpl.
  Check (plus_comm (eval a1) (eval a2)).
  apply (plus_comm (eval a1) (eval a2)).
Qed.

(* La bibliothèque standard de Coq contient une définition des
   inégalités comme propositions, par exemple *)

Check 1 <= 2.

Locate "<=".

(* On admet le lemme suivant *)
Lemma leq_minus : forall n m, n <= m -> n - m = 0.
Proof.
Admitted.

(* Prouvez la propriété suivante *)
Theorem Amo_leq : forall (a1 a2 : Aexp), eval a1 <= eval a2 -> eval (Amo a1 a2) = 0.
Proof.
  intros x y.
  apply leq_minus.
Qed.




(* ******************************************************************** *)
(** Extension de Aexp avec des variables et un état *)


 (*  On représente une variable par le constructeur Avas
     qui prend un nat (numéro de variable).
     Etendre le type Aexp pour prendre en compte les variables. *)


Inductive AexpV : Set := .
  (* Complétez ici *)

(* Un environnement est une fonction qui assigne une valeur à chaque (numéro de) variable *)

Definition env := nat -> nat.

(* Etendre la fonction sémantique aux expressions avec variables *)

Fixpoint evalV (a: AexpV) (s:env) : nat :=
  match a with

 (* Complétez ici *)

 end.

(** Evaluer l'expression correspondant à ((v1 + v2) * v3)
   dans l'état s1 suivant   *)

Definition s1 := fun v => match v with
                          | 1 => 5
                          | 2 => 9
                          | 3 => 3
                          | _ => 0
                          end.

Definition exp_3 := (* Complétez ici *).

Compute (evalV exp_3 s1).


(* Définissez une fonction env_agree_fp  : env -> env -> AexpV -> Prop
   tel que (env_agree_fp e1 e2 a) ssi e1 et e2 donnent les même valeurs
   aux variables de a. *)

Fixpoint env_agree_fp (e1 e2 : env) (a : AEexp) : Prop :=
(* compléter *)
.


Theorem env_agree_evalV_idem :
    forall a e1 e2, env_agree_fp e1 e2 a -> evalV a e1 = evalV a e2.
Proof.
  (* Complétez ici *)
Admitted.
