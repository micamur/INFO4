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

Nouveautés
- exists
- assert(nom := exp ).


*)

Require Import Arith.

(* ******************************************************************** *)
(** Extension de Aexp avec des variables et un état *)

(*  On représente une variable par le constructeur Ava
    qui prend un nat (numéro de variable).
    Etendre le type Aexp pour prendre en compte les variables. *)


Inductive AexpV : Set :=
  | Avas : nat -> AexpV
  | Ana : nat -> AexpV
  | Apl : AexpV -> AexpV -> AexpV
  | Amu : AexpV -> AexpV -> AexpV
  | Amo : AexpV -> AexpV -> AexpV
.

(* Un environnement est une fonction qui assigne une valeur à chaque (numéro de) variable *)

Definition env := nat -> nat.

(* Étendre la fonction sémantique aux expressions avec variables *)

Fixpoint evalV (a: AexpV) (s:env) : nat :=
  match a with
  | Avas v => s v
  | Ana n => n
  | Apl a1 a2 => evalV a1 s + evalV a2 s
  | Amu a1 a2 => evalV a1 s * evalV a2 s
  | Amo a1 a2 => evalV a1 s - evalV a2 s
end.

(* N.B. Le type de resultat est toujours un nat donc fonction NON DÉPENDANTE *)

(** Evaluer l'expression correspondant à ((v1 + v2) * v3)
   dans l'état s1 suivant   *)

Definition s1 := fun v =>
  match v with
  | 1 => 5
  | 2 => 9
  | 3 => 3
  | _ => 0
end.


(* Définir les expressions Aexp correspondant à
  - (1 * 2) + 3
  - (((1 + (2*3)) * 5) + (3*4))


Definition exp_2 := (Apl (Amu (Ana 1) (Ana 2)) (Ana 3)).

Definition exp_3 := (Apl (Amu (Apl (Ana 1) (Amu (Ana 2) (Ana 3))) (Ana 5)) (Amu (Ana 3) (Ana 4))).
 *)


Definition exp_3 := (Amu (Apl (Avas 1) (Avas 2)) (Avas 3)).

Definition env_agree_3 (e1 e2 : env) :=
  (e1 1 = e2 1 /\ e1 2 = e2 2) /\ e1 3 = e2 3.

Compute (evalV exp_3 s1).


(* Définir une fonction env_agree_fp  : env -> env -> AexpV -> Prop
   tel que (env_agree_fp e1 e2 a) ssi e1 et e2 donnent les même valeurs
   aux variables de a. *)

Fixpoint env_agree_fp (e1 e2 : env) (a : AexpV) : Prop :=
  match a with
  | Avas v => e1 v = e2 v
  | Ana n => True (* e1 et e2 toujours d'accord *)
  | Apl a1 a2
  | Amu a1 a2
  | Amo a1 a2 =>
      (env_agree_fp e1 e2 a1 /\ env_agree_fp e1 e2 a2)
end.

Compute (fun e1 e2 => env_agree_fp e1 e2 exp_3).

(* Deux environnements concordant sur les variables
   d'une expression lui donnent la même valeur *)

Theorem env_agree_evalV_idem :
    forall a e1 e2, env_agree_fp e1 e2 a -> evalV a e1 = evalV a e2.
Proof.
  intros a x y.
  induction a as [ v |              (* cas Avas *)
                   n |              (* cas Ana *)
                   a1 ha1 a2 ha2 |  (* cas Apl *)
                   a1 ha1 a2 ha2 |  (* cas Amu *)
                   a1 ha1 a2 ha2 ]; (* cas Amo *)
                 simpl.
  - intro H. apply H. (* apply (fun h => h) *)
  - reflexivity.
  - intro H ; destruct H as [h1 h2].
    pose (hh1 := ha1 h1).
    pose (hh2 := ha2 h2).
    rewrite hh1, hh2. (* on fait 2 rewrite en même temps avec la virgule *)
    reflexivity.
  - intros [h1 h2].
    apply f_equal2.
      + apply ha1, h1.
      + apply ha2, h2.
  - intro.
    apply f_equal2; auto.
(*
  - intros [h1 h2].
    rewrite ha1, ha2.
    reflexivity.
    + apply h2.
    + apply h1.
*)
Qed.

(* Check f_equal2. apply f_equal2. *)

(* Définition récursive d'une expression sans variables *)

Fixpoint SansVar (a:AexpV) :Prop :=
  match a with
  | Avas v => False
  | Ana n => True
  | Apl a1 a2
  | Amu a1 a2
  | Amo a1 a2 => (SansVar a1 /\ SansVar a2)
end.

(* Une expression sans variable s'évalue toujours pareil *)

Lemma SansVar_constant: forall a, SansVar a -> forall e1 e2, evalV a e1 = evalV a e2.
Proof.
  intros a H e1 e2.
  induction a as [ v |              (* cas Avas *)
                   n |              (* cas Ana *)
                   a1 ha1 a2 ha2 |  (* cas Apl *)
                   a1 ha1 a2 ha2 |  (* cas Amu *)
                   a1 ha1 a2 ha2 ]; (* cas Amo *)
                 simpl.
  - hnf in H. destruct H. (* hypothèse False donc destruct suffit *)
  - reflexivity.
  - hnf in H. destruct H as [h1 h2].
    pose (hh1 := ha1 h1).
    pose (hh2 := ha2 h2).
    rewrite hh1, hh2.
    reflexivity.
    (* apply ha1 in h1. *)
  - hnf in H. destruct H as [h1 h2]. auto.
  - hnf in H. destruct H as [h1 h2]. auto.
Qed.

(* Montrer que la réciproque est fausse (distinction syntaxe/sémantique) *)

Lemma constant_non_SansVar: exists a, (forall e1 e2, evalV a e1 = evalV a e2) /\ ~ SansVar a.
Proof.

  (* TODO à compléter *)

Qed.

(* Montrer que  "a est sans variable" <-> 
   "tout les environnements coincident pour a" *)

Lemma SansVar_all_env_agree: forall a, SansVar a <-> (forall e1 e2, env_agree_fp e1 e2 a).
Proof.

  (* OPTIONNEL, DIFFICILE à garder pour la fin *)
  (* TODO à compléter *)

Qed.


(* un environnement est plus petit qu'un autre si toutes les variables y sont 
   plus petites *)

Definition env_le (e1 e2:env) := forall v , e1 v <= e2 v.

(* une expression est monotone (croissante) si sa valeur augmente avec celle
   des variables *)

Definition monotonic (a:AexpV) := 
  forall e1 e2,  env_le e1 e2 -> evalV a e1 <= evalV a e2.

(* Propriétés de monotonie de + * et - *)

Lemma le_self: forall m, m <= m.
  left.
Qed.

Lemma add_le_mono: forall m n p q, m <= n -> p <= q -> m+p <= n+q.
  apply Nat.add_le_mono.
Qed.

Lemma mul_le_mono: forall m n p q, m <= n -> p <= q -> m*p <= n*q.
  intros;apply Nat.mul_le_mono_nonneg;auto;apply Nat.le_0_l.
Qed.

Lemma sub_le_mono: forall m n p q, m <= n -> p = q -> m-p <= n-q.
  intros;subst;apply Nat.sub_le_mono_r;auto.
Qed.

(* Mq si il n'y a pas de variable à droite des soustractions, alors l'expression est croissante. *)

(* Définition d'une expression sans variable à droite d'une soustraction *)

Fixpoint SansVarApresMoins (a:AexpV) :Prop :=

  (* TODO à compléter *)

  end.

(* Une expression SansVarApresMoins est croissante *)

Lemma SansVarApresMoins_monotonic : forall a, SansVarApresMoins a -> monotonic a.
Proof.

    (* TODO à compléter *)

Qed.

(* Expressions equivalentes == même valeur pour tous environnement *)

Definition sem_equal a1 a2 := forall e, evalV a1 e = evalV a2 e.

(* Toute expression constante est équivalente à une constante *)

Lemma sem_equal_constant: forall a, (forall e1 e2, env_agree_fp e1 e2 a) ->
                                    exists n, sem_equal a (Ana n).
  Proof.

    (* OPTIONNEL *)
    (* TODO à compléter *)

  Qed.
