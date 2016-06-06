#ifndef QUICKSORT_H
#define QUICKSORT_H

#include <stddef.h>
#include "basetype.h"
#include "array_double.h"

/*@ requires \valid(array+(l..h));
  @ requires l <= h;
  @
  @ assigns array[l..h];
  @ 
  @ ensures gt_array_double(array, l, \result - 1, array[ \result ]);
  @ ensures lte_array_double( array, \result + 1, h, array[ \result ]); 
  @ ensures permut_double{Pre, Post}(array, array, l, h);
  @ ensures l <= \result <= h;
*/

size_t partition_double(double* array, const size_t l, const size_t h);

/*@ requires \valid(array+(l..h));
  @ requires l <= h;
  @
  @ assigns array[l..h];
  @ ensures ordered_array_double(array, l , h);
  @ ensures permut_double{Pre, Post}(array, array, l, h);
*/

void quicksort_double(double* array, const size_t l, const size_t h);

#endif
