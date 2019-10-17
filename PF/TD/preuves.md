# PF - Preuves (Mica Murphy)

## Preuve 1 - neutralité à droite de `[]` pour `@`

- Cas de base :

	```text
	[] @ [] = [] (trivial)
	```

- Cas récursif :

	```text
	Supposons que l@[] = l et montrons que (c::l)@[] = c::l est vrai
	(avec c::l l'ajout de l'élément c à gauche de l)

	(c::l) @ [] = c::(l@[])  (trivial pour un élément)
	            = c::l       (par hypothèse d'induction)
	            Qed
	```

- On a bien vérifié la propriété

## Preuve 2 - associativité de `@`

- Cas de base : (`l1 = []`)

	```text
	([] @ l2) @ l3 = (l2) @ l3 = (l2 @ l3) = [] @ (l2 @ l3) (par neutralité)
	```

- Cas récursif : (`l1` -> `c::l1`)

	```text
	Supposons que (l1@l2)@l3 = l1@(l2@l3) est vrai,
	montrons que ((c::l1)@l2)@l3 = (c::l1)@(l2@l3) est vrai

	((c::l1) @ l2) @ l3 = (c::(l1 @ l2)) @ l3  (trivial pour un élément)
	                    = c::((l1 @ l2) @ l3)  (trivial pour un élément)
	                    = c::(l1 @ (l2 @ l3))  (par hypothèse d'induction)
	                    = (c::l1) @ (l2 @ l3)  (trivial pour un élément)
	                  	Qed
	```

- On a bien vérifié la propriété