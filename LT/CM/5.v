(** * Fonctions avec types dépendants *)

Inductive coulfeu : Set :=
  | vert : coulfeu
  | orange : coulfeu
  | rouge : coulfeu.

Inductive arbin : Set :=
  | V : arbin
  | N : arbin -> coulfeu -> arbin -> arbin.

Definition ab1 : arbin := N V vert V.
Definition ab2 : arbin := N ab1 rouge ab1.
Definition ab3 : arbin := V.

Definition coulsuiv : forall c : coulfeu, coulfeu :=
  fun c =>
  match c with
  | vert => orange
  | orange => rouge
  | rouge => vert
  end.

Definition f1 : forall c : coulfeu, arbin :=
  fun c =>
  match c with
  | vert => ab1
  | orange => ab2
  | rouge => ab3
  end.

Check (forall _:coulfeu,coulfeu).

Definition f2 : forall c : coulfeu -> Set :=
  fun c =>
  match c with
  | vert => arbin
  | orange => coulfeu
  | rouge => coulfeu -> arbin
  end.

Variable c:coulfeu.
Eval Compute in (f2 c).

(** SCOOP : en Coq on peut aussi calculer des types *)

Definition scoop : forall c : coulfeu, f2 c :=
  fun c =>
  match c with      (* de type f2 c *)
  | vert => ab2     (* de type (f2 c) [c:=vert] == f2 vert == arbin *)
  | orange => rouge (* de type (f2 c) [c:=orange] == f2 orange == coulfeu *)
  | rouge => f1     (* de type (f2 c) [c:=rouge] == f2 rouge == (coulfeu -> arbin) *)
  end.

(** Le type du résultat de scoop DÉPEND de son argument [c] :
     le type de scoop vert est arbin, celui de scoop orange est coulfeu
     celui de scoop rouge est coulfeu -> arbin
*)

Compute scoop orange.
Definition fuor : coulfeu := scoop orange.
Compute fuor.

Eval compute scoop (coulsuiv orange).
Definition fucsor : coulfeu -> arbin := scoop (coulfeu orange).
Compute fcsuor.

(** A-> B est juste une abréviation pour forall x:A, B, lorsque B
    ne DÉPEND PAD de x
*)

Check coulsuiv.
Check (forall c : coulfeu, coulfeu).

(** Chacun connaît la règle de typage de l'application d'une fontion :

    f : A -> B    e : A
    -------------------
          f e : B

    f : forall _:A, B    e : A
    -------------------------
              f e : B (* sans sucre syntaxique *)

    On a la même chose lorsque la fonction a un type dépendant :

    f : forall x:A, B    e : A
    --------------------------
             f e : B (* manque la substitution *)

    Sauf qu'il faut se souvenir qu'ici, après application, le type de f e
    dépend de x : c'est donc non pas B, mais B dans lequel x a été substitué par e

    Dans l'exemple ci-dessus, scoop joue le rôle de f, B serait f2 x;
    en prenant par exemple orange dans le rôle de e, le type de f e est
    non plus f2 x mais f2 orange.
    D'une manière plus générale, on l'écrit B[x := e] pour indiquer
    "B soumis à la substitution de x par e".

    f : forall x:A, B    e : A
    --------------------------
          f e : B[x := e]

    Exemple :

    scoop : forall x:coulfeu, f2 x    orange : coulfeu
    --------------------------------------------------
                scoop orange : f2 orange
*)

Definition scoop_i : forall c : coulfeu, f2 c.
  (* Show Proof. *)
  intro c.
  (* Show Proof. *)
  destruct c.
  - simpl. apply ab2.
  - apply rouge.
  - simpl. apply f1.
Defined.

Print scoop_i.
Print scoop.

(* On peut définir n'importe quelle fonction intéractivement *)

Definition coulsuiv_i : forall c : coulfeu, coulfeu.
  intro c.
  destruct c.
  - apply orange.
  - apply rouge.
  - apply vert.
Defined.

Print coulsuiv_i.
Print coulsuiv.

(** Et pas seulement les fonctions *)

Definition exemple_2-applications : arbin := f1 (coulsuiv vert).

Definition exemple_2-applications_i : arbin.
  Check f1.
  apply f1.
  Check coulsuiv.
  apply coulsuiv.
  apply vert.
Defined.






.
