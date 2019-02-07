/* ****************************************************************************
                              MAXIMUM D'UN TABLEAU

   L'énoncé est introduit sous la forme de commentaires C. Les différents
   morceaux de programme et de spécification à considérer sont mentionnés en
   programmation littéraire :

              https://en.wikipedia.org/wiki/Literate_programming

   ************************************************************************* */

/* ---------------------------------------------------------------------------
   Cet exercice est une variation de l'exercice "Maximum d'un tableau" du TD
   6. Cet exercice n'a pas été corrigé en cours, mais si vous avez pris le temps
   de le faire par vous-même comme je l'avais demandé, cela devrait vous
   permettre de gagner un peu de temps pour ce TP noté...
   ------------------------------------------------------------------------- */

/* ---------------------------------------------------------------------------
   La fonction [max_idx] est une fonction auxiliaire de la fonction principale
   [max_seq], définie juste après. Nous ne donnons ici que sa déclaration. Sa
   définition est fournie en fin de fichier.
   ------------------------------------------------------------------------- */

int max_idx(unsigned int *t, int len);

/* ---------------------------------------------------------------------------
   La fonction [max_seq] retourne la valeur maximale contenue dans
   le tableau [t] de longueur [len]. Elle retourne -1 si le tableau est vide.

   Question 1 : spécifier cette fonction en utilisant des comportements ACSL.

   Question 2 : prouver cette fonction, y compris sa terminaison et l'absence
   d'erreurs à l'exécution. On prendra garde à ne spécifier que les
   préconditions strictement nécessaires pour garantir l'absence d'erreurs à
   l'exécution.

   Indice : il est autorisé d'inclure un fichier de la bibliothèque standard du
   C (déjà utilisé en TD dans des cas similaires).
   ------------------------------------------------------------------------- */

int max_seq(unsigned int *t, int len) {
  if (len <= 0) return -1;
  return t[max_idx(t, len)];
}

/* ---------------------------------------------------------------------------
   Ci-après, la définition de la fonction [max_idx].
   ------------------------------------------------------------------------- */

int max_idx(unsigned int *t, int len) {
  int max = 0;
  for(int i = 1; i < len; i++)
    if (t[max] < t[i])
      max = i;
  return max;
}
