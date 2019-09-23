(** INITIATION A COQ *)

(* 
Le contenu de ce fichier aura été vu en cours.
Il est conseillé de le refaire :
- très vite en début de TD si besoin, sans les exercices
  proposés en fin de fichier
- à la maison, avec ces exercices
*)

(** * Types, fonctions et preuves élémentaires *)

(** Coq est primitivement un langage de programmation particulier.
    Comme OCaml, c'est un langage fonctionnel typé.
    Son système de types est beaucoup plus riche que celui de OCaml,
    ce qui permet en particulier d'énoncer des formules logiques,
    et éventuellement de les démontrer.

    Dans un premier temps, on se focalise sur l'aspect programmation,
    et les formules logiquees considérées sont de simples égalités.
 *)

(** ** Généralités *)

(** Un script Coq est une suite de déclarations de types, de valeurs,
    (très souvent : des fonctions), d'énoncés de théorèmes suivis
    de leur preuve.

    On a également des requêtes pour obtenir des informations,
    calculer des espressions.
*)

(** À RETENIR : EN COQ, TOUT FINIT PAR UN POINT '.' *)

(** ** Types énumérés *)

(** Le type qui s'écrirait en OCaml
type coulfeu =
  | Vert
  | Orange
  | Rouge

se définit en Coq presque de la même façon
*)

Inductive coulfeu : Set :=
  | vert : coulfeu
  | orange : coulfeu
  | rouge : coulfeu
.

(** Noter les différences *)

(** ** Définition d'une valeur fonctionnelle *)

Definition coul_suiv : coulfeu -> coulfeu :=
  fun c =>
    match c with
    | vert => orange
    | orange => rouge
    | rouge => vert
    end.

(** ** Premier théorème *)
Example ex1_coul_suiv : coul_suiv (coul_suiv vert) = rouge.
Proof. simpl. reflexivity. Qed.

(** Une *tactique* est une commande permettant de faire progresser une preuve *)

(** On a utilisé ci-dessus les tactiques suivantes :
    - simpl : simplification par calcul
    - reflexivity : reconnaissance que les deux membres de l'égalité
                    à prouver sont identiques.
 *)

(** ATTENTION À BIEN TERMINER PAR "Qed." *)

(** Une autre définition qui va servir d'abréviation *)

Definition cs := coul_suiv.

(** Ici on a laissé Coq deviner le type de cs.
    On peut vérifier le type de cs. *)

Check cs.


(** ** Variables *)

(** Les preuves par réflexivité fonctionnent non seulement
    entre des expressions constantes identiques, mais aussi
    entre des expressions comportant des variables *)

(** On a la possibilité en Coq (mais pas en OCaml) de déclarer
    des variables :
    ce sont des noms dont on connaît simplement le type.
    Il faut que ces noms soient déclarés dans une portée
    (domaine de visibilité) définie par une section.
*)

(** Ouverture d'une section dans laquelle on va faire quelques
    preuves par réflexivité *)

Section sec_refl.
  Variable c : coulfeu.

  Theorem th1_refl_simple : c = c.
  (** Remarquer que le but contient un environnement comportant
      l'hypothèse c : coulfeu *)
  Proof. reflexivity. Qed.

  (** Tactique unfold *)
  Theorem th2_refl : cs c = coul_suiv c.
  Proof. unfold cs. reflexivity. Qed.

  (** Observer l'effet de unfold. Expliquer la preuve *)


(** Fermeture de la section *)
End sec_refl.


(** ** Principe de Leibniz : tactique rewrite *)

Section sec_reec.
  Variable c : coulfeu.
  Hypothesis crou : c = rouge.

  Theorem cs_rouge : cs c = vert.
  Proof.
    rewrite crou.
    simpl.
    reflexivity.
  Qed.

End sec_reec.

(** ** Raisonnement par cas : tactique destruct *)

Section sec_cas.
  Variable c : coulfeu.

  Theorem th3_cs : cs (cs (cs c)) = c.
  Proof.
    (** reflexivity de fonctionne pas *)
    Fail reflexivity.
    (** Il faut raisonner par cas sur les trois valeurs de [c] possibles *)
    destruct c.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

End sec_cas.

(** ** Raisonnement universel : tactique intro *)

(** Il est possible d'énoncer des formules quantifiées universellement.
    Par exemple : forall c : coulfeu, c = c.
 *)

Theorem th_refl_gen : forall c : coulfeu, c = c.
Proof.
  (** Pour la démontrer, la première étape consiste à indiquer
      "soit c0 une couleur arbitraire, démontrons c0 = c0." *)
  intro c0.
  (** Remarquer que intro a introduit l'hypothèse c0 : coulfeu *)
  (** On a déjà vu que reflexivity fonctionne dans cette situation *)
  reflexivity.
Qed.

Theorem th_crou_gen : forall c : coulfeu, c = rouge -> cs c = vert.
Proof.
  intro c0. intro c0rou. rewrite c0rou. simpl. reflexivity.
Qed.

(** Variante avec section *)

Section sec_variante_th_crou_gen.
  Variable c : coulfeu.
  Theorem th_crou_demi_gen : c = rouge -> cs c = vert.
  Proof.
    (* Complétez ici *)
  Admitted.

End sec_variante_th_crou_gen.


(** * Conjonctions et disjonctions de propositions *)

(*
Les exemples de preuves vues ci-dessus sont des preuves d'égalités.
Très souvent on a besoin de combiner des propositions.
Les connecteurs principaux sont :
- l'implication entre deux propositions "P implique Q" notée P -> Q
  déja utilisée auparavant
- la conjonction de deux propositions "P et Q" notée P /\ Q
- la disjonction de deux propositions "P ou Q" notée P \/ Q.

Nous avons également vu auparavant que l'on pouvait utiliser
la quantification universelle (∀) notée en toutes lettres forall.

Remarque importante : en "logique propositionnelle", on explique souvent
les combinaisons de propositions au moyen d'un calcul de valeurs de vérité
(l'algèbre booléenne que chacun connaît). Mais ce n'est pas suffisant
dès que l'on prend des logiques plus réalistes aptes à raisonner (par
exemple par récurrence) sur des infinités d'objets.
On adopte donc un autre point de vue dans lequel une proposition c'est 
quelque chose que l'on peut prouver,
c'est-à-dire qui peut se déduire au moyen de démonstrations, 
ces dernières étant présentées sous forme d'arbre.

Les règles de déduction qui gouvernent /\ et \/ sont issues
de la déduction naturelle, rappelée en cours.

En pratique,
- pour la disjonction :
  - pour prouver P \/ Q, on choisit ultimement
    soit de prouver P au moyen de la tactique left
    soit de prouver Q au moyen de la tactique right
  - si l'on a une hypothèse poq :  P \/ Q en hypothèse,
    on peut raisonner dessus par cas au moyen de la tactique destruct
    de la façon suivante :
    destruct poq as [p | q]
- pour la conjonction :
  - pour prouver P /\ Q, on doit ultimement 
    prouver P d'une part et Q d'autre part, au moyen de la tactique split
  - si l'on a une hypothèse peq :  P /\ Q en hypothèse,
    on peut la décomposer en deux hypothèses au moyen de la tactique destruct
    de la façon suivante :
    destruct peq as [p q]
- pour l'implication :
  - pour prouver P -> Q, on introduit une nouvelle hypothèse p:P
    à partir de laquelle on prouve Q, au moyen de la tactique intro p
  - si l'on a une hypothèse piq :  P -> Q en hypothèse,
    on peut l'exploiter lorsque la conclusion à démontrer est Q
    au moyen de la tactique apply piq
    (il reste alors à démontrer P)
*)

(** Exercices/exemples triviaux *)

Section prop.

  Variables P Q : Prop.
  Lemma conj_com :  P /\ Q -> Q /\ P.
  Proof.
  Admitted.

Lemma disj_com : P \/ Q -> Q \/ P .
  Proof.
  Admitted.

End prop.


(** * Exercices complémentaires *)

(** Définir un type traffic_light, une version anglaise de coulfeu *)

(* Complétez ici *)

(** Définir une fonction de traduction de coulfeu vers traffic_light *)

(* Complétez ici *)

(** Définir une fonction de traduction de traffic_light vers coulfeu *)

(* Complétez ici *)

(** Énoncer et démontrer des théorèmes indiquant que ces fonctions
    sont inverses l'une de l'autre  *)

(* Complétez ici *)
