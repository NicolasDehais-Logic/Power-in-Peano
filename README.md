Ce projet a été réalisé sur **Rocq V9.1.0**.



Le fichier principal est *power\_in\_peano.v*.

*Decidability.v* est un fichier annexe que j’ai rédigé contenant quelques outils de raisonnement. Il contient:

* une tactique dec\_simpl pour prouver la décidabilité d’une formule à partir de ses composantes atomiques, en utilisant des lemmes triviaux permettant de traiter chaque combinaison de cas;
* une tactique strong\_induction pour le raisonnement par récurrence forte (bien que cela n’ait pas de rapport direct avec la décidabilité);
* un lemme smallest\_element qui prouve l’axiome du plus petit élément pour les propriétés décidables.

Il est finalement assez peu utilisé par le fichier principal.

