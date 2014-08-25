#ifndef BASETYPE_H
#define BASETYPE_H

#include <stddef.h>
#include "basetype.h"

/*@ inductive permut_double{L1, L2}(double *a1, double *a2, integer l, integer h){
  @ case permut_double_refl{L1, L2}:
  @      \forall double *a1, *a2, integer l, h;
  @              (\forall integer k; l <= k <= h ==> \at(a1[k], L1) == \at(a2[k], L2)) ==> permut_double{L1, L2}(a1, a2, l, h);
  @ case permut_double_swap{L1, L2}:
  @      \forall double *a1, *a2, integer l, h, i, j;
  @              (\forall integer k; l <= k <= h ==> k != i ==> k != j ==> \at(a1[k], L1) == \at(a2[k], L2)) ==> 
  @              (\at(a1[i], L1) == \at(a2[j], L2) && \at(a1[j], L1) == \at(a2[i], L2)) ==>
  @              permut_double{L1, L2}(a1, a2, l, h);
  @ case permut_double_trans{L1, L2, L3}:
  @      \forall double *a1, *a2, *a3, integer l, h;
  @      permut_double{L1, L2}(a1, a2, l, h) ==> permut_double{L2, L3}(a2, a3, l, h) ==> permut_double{L1, L3}(a1, a3, l, h);
  @ case permut_double_compo{L1, L2}:
  @      \forall double *a1, *a2, integer l, i, h;
  @      permut_double{L1, L2}(a1, a2, l, i) ==> permut_double{L1, L2}(a1, a2, i, h) ==> permut_double{L1, L2}(a1, a2, l, h);
  @ 
  @ }
*/




/*@ requires \valid(array+(l..h));
  @ requires l <= h;
  @
  @ assigns array[l..h];
  @ 
  @ ensures \forall integer k; l <= k < \result ==> array[k] < array[\result];
  @ ensures \forall integer k; \result <= k <= h  ==> array[\result] <= array[k]; 
  @ ensures permut_double{Pre, Post}(array, array, l, h);
*/

size_t partition_double(double* array, const size_t l, const size_t h);

/*@ requires \valid(array+(l..h));
  @ requires l <= h;
  @
  @ assigns array[l..h];
  @ ensures \forall integer k; l <= k < h ==> array[k] <= array[k+1];
  @ ensures permut_double{Pre, Post}(array, array, l, h);
*/

void quicksort_double(double* array, const size_t l, const size_t h);



#endif
