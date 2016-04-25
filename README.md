#####Aux étudiants M1 de l'UE *Preuves et démonstrations automatisées*

---------------------------

Bonjour à tous,

Comme indiqué en TP, voici les instructions pour la réalisation
du projet correspondant à l'UE *Preuves et démonstrations automatisées.*

Vous pouvez télécharger l'archive du projet via l'interface
de GitHub (Download ZIP) oubien cloner le projet via

```
git clone https://github.com/DmxLarchey/PHP-etudiants.git
```

Une fois dans le repertoire des fichiers *.v (code source Coq),
vous pouvez taper les commandes

```
make
coqide *.v & 
```

Je vous rappelle que le but du projet est de 
**compléter les preuves manquantes** ou 
partiellement manquantes dans les fichiers
**perm.v**, **list_ind.v**, **list_incl.v** et 
**list_pigeon_hole.v** (elles contiennent de *admit* et/ou se
terminent par *Admitted.*) Quand vous aurez terminé,
toutes vos preuves devraient se terminer par *Qed* et ne
doivent plus contenir la tactique *admit*.

Le résultat de votre travail est à me rendre par email
(larchey@loria.fr) à la date du Mardi 16 Mai. Le travail
est **individuel** même si vous pouvez échanger des idées
entre vous pour résoudre les exercices. N'oubliez pas
de consulter la documentation en ligne de Coq

http://coq.inria.fr/documentation

Je vous rappelle en outre qu'aucune preuve nouvelle n'est
à inventer, elles ont toutes été *réalisées à la main* lors du
cours. Votre travail est la mise en oeuvre formelle de ces
preuves informelles dans l'outil Coq.

Enfin, nous organiserons une **soutenance sur machine** d'une
durée individuelle d'environ 15 minutes à la date du Jeudi 18 Mai, 
où vous nous présenterez le résultat de
votre travail et nous exposerez les éventuelles difficultés
que vous avez rencontrées.

Bon travail

Dominique Larchey-Wendling

