/* ****************************************************************************
                              TRI PAR INSERTION

   L'énoncé est introduit sous la forme de commentaires C. Les différents
   morceaux de programme et de spécification à considérer sont mentionnés en
   programmation littéraire :

              https://en.wikipedia.org/wiki/Literate_programming

   ************************************************************************* */

/* ---------------------------------------------------------------------------
  Complément sur ACSL :
   
  En ACSL, les fonctions logiques et les prédicats peuvent être étiquetés par
  un ou plusieurs points de programme spécifiés entre accolades. Par exemple,
  \valid{P}(p) indique que le pointeur p est valide au point de programme P, 
  ce qui est exactement équivalent à \at(\valid(p), P).
  
  Une étiquette omise est par défaut équivalente à Here. Ainsi \valid(p) est
  équivalent à \valid{Here}(p), c'est-à-dire à \at(valid(p), Here). 
   ------------------------------------------------------------------------- */

/* ---------------------------------------------------------------------------
   L'axiomatique [Nb_occ] suivante est là pour vous aider dans la suite de
   l'exercice. Elle définit une fonction logique [nb_occ].

   Question 1 : expliquer en langue naturelle (français ou anglais) chacun des
   trois axiomes composant cette axiomatique. En déduire une spécification
   informelle de [nb_occ].
   ------------------------------------------------------------------------- */

/*@ axiomatic Nb_occ {
  @ 
  @   logic integer nb_occ{L}(int* a, integer start, integer stop, integer v)
  @     reads a[start..stop];
  @   
  @   axiom no_elt{L}:
  @     \forall int* a, integer start, stop, v;
  @       stop < start ==> nb_occ{L}(a, start, stop, v) == 0;
  @   
  @   axiom occurs{L}:
  @     \forall int* a, integer start, stop, v, idx;
  @       start <= idx <= stop && a[idx] == v ==>
  @       nb_occ{L}(a, start, stop, v) ==
  @         1 + nb_occ{L}(a, start, idx-1, v) + nb_occ{L}(a, idx+1, stop, v);
  @     
  @   axiom not_occurs{L}:
  @     \forall int* a, integer start, stop, v, idx;
  @       start <= idx <= stop && a[idx] != v ==>
  @       nb_occ{L}(a, start, stop, v) ==
  @         nb_occ{L}(a, start, idx-1, v) + nb_occ{L}(a, idx+1, stop, v);
  @ }
  @ 
  @*/

/* ---------------------------------------------------------------------------
   Petit rappel de mathématiques élémentaires à toutes fins utiles :
   
   Une permutation est une bijection d'un ensemble dans lui-même : l'ensemble
   résultant doit contenir les mêmes éléments que l'ensemble de départ (et en
   mêmes nombres), éventuellement dans un ordre différent.

   Exemple : { 0; 1; 1; 2; 3 } est une permutation de { 1; 2; 3; 1; 0 },
   mais pas { 0; 1; 2; 3 }.
   ------------------------------------------------------------------------- */

/* ---------------------------------------------------------------------------
   Les trois prédicats [is_sorted], [same_elt] et [exchange] vous seront aussi
   potentiellement utiles pour résoudre la question principale (la question 3).

   Question 2 : compléter le corps de ces trois prédicats de manière à ce qu'ils
   satisfassent leurs spécifications informelles.
   ------------------------------------------------------------------------- */

/*@ // [is_sorted(a, start, stop)] est valide si et seulement si le tableau [a] 
  @ // est trié entre les indices [start] et [stop] (inclus).
  @ predicate is_sorted(int* a, integer start, integer stop) =
  @   \false; // remplacer \false par la définition du prédicat
  @
  @ // [is_permutation{L1,L2}(a, start, stop)] est valide si et seulement si les
  @ // éléments du tableau [a] au point de programme [L1] et entre les indices
  @ // [start] et [stop] (inclus) est une permutation des mêmes éléments du
  @ // même tableau au point de programme [L2].
  @ predicate is_permutation{L1,L2}(int* a, integer start, integer stop) =
  @   \false; // remplacer \false par la définition du prédicat
  @ 
  @ // [exchange{L1,L2}(a, start, stop, i, j)] est valide si et seulement si
  @ // les éléments du tableau [a] aux cases d'indices [i] et [j] (variant
  @ // entre [start] et [stop] inclus) ont été échangés entre les points de 
  @ // programme [L1] et [L2].
  @ predicate exchange{L1,L2}
  @   (int *a, integer start, integer stop, integer i, integer j) =
  @   start <= i <= stop && start <= j <= stop
  @   && \at(a[i],L1) == \at(a[j],L2) && \at(a[j],L1) == \at(a[i],L2)
  @   && \forall integer k; start <= k <= stop ==> k != i ==> k != j
  @        ==> \at(a[k],L1) == \at(a[k],L2);
  @*/

/* ---------------------------------------------------------------------------
   Le lemme [is_permutation_after_exchange] est un lemme technique aidant à
   l'automatisation des preuves.

   IL N'EST PAS DEMANDÉ DE LE PROUVER.

   Question 3 : donner une spécification informelle (en français ou en anglais) 
   de ce lemme.
   ------------------------------------------------------------------------- */

/*@ lemma is_permutation_after_exchange_DO_NOT_PROVE_IT{L1,L2}:
  @   \forall int *a; \forall integer start, stop, i, j;
  @   exchange{L1,L2}(a, start, stop, i, j) ==>
  @   is_permutation{L1,L2}(a, start, stop);
  @*/

/* ---------------------------------------------------------------------------
   La fonction [swap] est une fonction auxiliaire de la fonction principale
   [sort], définie juste après. Nous ne donnons ici que sa déclaration. Sa
   définition est fournie en fin de fichier.
   ------------------------------------------------------------------------- */

void swap(int *a, int i, int j);

/* ---------------------------------------------------------------------------
   La fonction [sort] trie le tableau [a] de longueur [len] de manière
   croissante. L'algorithme de tri utilisé ici est appelé "tri par insertion".

   Question 4 : modifier l'assertion [ex] à la fin de la boucle principale de
   manière à exprimer que les éléments des cases d'indices [i] et [low] ont été
   échangés entre le point de programme [L] et celui où l'assertion est écrite.

   Cette assertion peut être nécessaire pour l'automatisation de la preuve.

   Question 5 : spécifier et prouver la fonction [sort], y compris sa
   terminaison et l'absence d'erreurs à l'exécution.
   ------------------------------------------------------------------------- */

void sort(int* a, int len) {
  int i;
  for(i = 0; i < len; i++) {
    int low = i;
    for(int j = i + 1; j < len; j++)
      if (a[j] < a[low]) low = j;
  L: if (i != low) swap(a, i, low);
    /*@ assert ex: \false; */
  }
}

/* ---------------------------------------------------------------------------
   Ci-après, la définition de la fonction [swap].
   ------------------------------------------------------------------------- */

void swap(int *a, int i, int j) {
  int tmp = a[j];
  a[j] = a[i];
  a[i] = tmp;
}
