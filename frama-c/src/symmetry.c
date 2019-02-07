/* ****************************************************************************
                              MATRICE SYMÉTRIQUE

   L'énoncé est introduit sous la forme de commentaires C. Les différents
   morceaux de programme et de spécification à considérer sont mentionnés en
   programmation littéraire :

              https://en.wikipedia.org/wiki/Literate_programming

   ************************************************************************* */

/* ---------------------------------------------------------------------------
   Petits rappels de mathématiques élémentaires à toutes fins utiles :
 
   - Une matrice carrée de taille N (N, entier naturel) est une matrice
   possédant N lignes et N colonnes.

   - Une matrice carrée A est dite symétrique si et seulement si A_{ij} =
   A_{ji} pour toute ligne [i] et colonne [j].
   ------------------------------------------------------------------------- */

#include <stdbool.h>

/* ---------------------------------------------------------------------------
   La fonction [is_symmetric] ci-dessous retourne [true] si et seulement si
   [matrix] est une matrice symétrique de taille [len]. Elle retourne [false]
   sinon.

   Question 1 : spécifier cette fonction en utilisant des comportements ACSL.

   Question 2 : prouver cette fonction, y compris sa terminaison et l'absence
   d'erreurs à l'exécution.
   ------------------------------------------------------------------------- */

_Bool is_symmetric(int **matrix, int len) {
  for (int i = 0; i < len; i++)
    for (int j = 0; j < i; j++)
      if (matrix[i][j] != matrix[j][i])
        return false;
  return true;
}
