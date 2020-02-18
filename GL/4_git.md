# GL - Git

Côté client :

```bash
git init # toto/.git/config
git commit
remote add server url # server est en général origin
push -u server master # publier la branche master sur server
```

Côté serveur :

```bash
git init --bare # toto.git/config
```

Hiérarchie des branches : `dev1/F1` et `dev2/F2` par exemple.

`rebase` pour "déplacer" des branches, réorganiser.

`revert`, `amend` et `reset` pour nettoyer un dépôt ou réparer des bêtises, reversionner correctement.

*Exemple.* `git commit --amend -m "Toto sans typo"`

`reset` a 3 types : `--hard`, `--soft` et sans option

Pour travailler à plusieurs on peut par exemple travailler tous sur le même dépôt distant ou bien chacun sur son propre dépôt distant et en faisant des forks et des pull requests (décentralisé).



.
