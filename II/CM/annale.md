# II Annales

## Examen de 2017-2018

Sujet : <http://iihm.imag.fr/blanch/INFO4/IHM/exams/2017-2018-RICM4-IHM.pdf>

### Question 7

Éléments qui changent de taille :

- VBox, HBox = ne change pas de taille quand redimentionné
- BorderPane = change de taille quand redimentionné
  - La partie centrale de la boîte de réception grandit avec la fenêtre
  - Le vide au milieu de la première barre d'outils aussi

```text
         Stage (fenêtre)
           |
         Scene (contenu de la fenêtre)
           |
       BorderPane
     top /       \ center
      VBox     [Centre]
     /    \
[Barre1] [Barre2]

[Barre1]
   BorderPane
left /    \
  HBox    TextField
  //|\\
(5 Button)

[Barre2]
                  HBox
            /    /    | \ \
ToggleButton ComboBox (3 Button)

[Centre]
                SplitPane(H)
          /                     \
  BorderPane                   SplitPane(V)
bottom /  \ center               /        \
 FlowPane TreeTableView  TreeTableView TextArea
  / | \
(3 Button)
```

## Examen 2018-2019

### Question 1, services pour l'intéraction, Fekete (extrait CM 2)

D'après Fekete (1996), le NF doit offrir des **services nécessaires** à l’interaction :

- **La notification**
  - C'est la possibilité pour un module externe d'être prévenu lorsque l'état du NF change.
  - *Par exemple, si le système de fichiers (FS) l'implémente, une application visualisant une partie du FS peut être notifiée et réaffichée si le FS est modifié, ainsi elle est continuellement à jour.*
- **La prévention des erreurs**
  - C'est la possibilité de savoir si un appel de fonction est licite dans un contexte.
  - *Par exemple, lorsque des objets graphiques sont sélectionnés, les items de menu agissant sur la sélection doivent être désactivés si leur activation produit une erreur.*
- **L’annulation**
  - C'est la possibilité de revenir à des états précédents du NF.
  - *Par exemple, dans un FS pour annuler la suppression d'un fichier.*

Source : <https://pdfs.semanticscholar.org/fbd6/4bfa055a8481956f89f873b079fa2f9ba140.pdf>

### Question 2, modèle de Seehiem

L'UI peut se décomposer en trois parties correspondant chacune à un niveau :

- Présentation, niveau lexical : mots (ClicDown, Move, ClicUp)
- Contrôleur de dialogue, niveau syntaxique : phrase (drag-n-drop)
- Interface du NF, niveau sémantique : action, évaluation (déplacement du fichier)

Les boîtes à outils de construction d'interface (ou OS et systèmes de fenêtrage) fournissent le niveau lexical mais aussi le niveau syntaxique (au moins en partie). Le niveau sémantique ne peut pas être fourni comme il est dépendant du type d'application.

### Question 3

a. Problème identifié dans le code : alors qu'on est dans le package `nf` on modifie un bout de l'interface dans la classe `UIUpdater`, le principe numéro 2 n'est pas respecté (le NF n'est pas indépendant de l'UI).
b. Solution générale : fournir un service de notification à qui on va passer la nouvelle valeur quand elle change (l'interface peut s'abonner). Plus simplement on peut enlever la boucle du NF et on la colle dans l'UI (= *polling*).

### Question 4

```java
public void handle(IE e) {
  switch(state) {
    case IDLE:
    switch(e.getEventType().getName()) {
      case "MOUSE_PRESSED":
      s = new Segment(e.getPoint());
      state = State.MOTION;
      break;
    }
  }
}
```
