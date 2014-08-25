#include "quicksort.h"

size_t partition_double(double* array, const size_t l, const size_t h){

  size_t pivot_index = l + (h - l) /2;

  double pivot_value = array[pivot_index];

  {
    double tmp = array[h];
    array[h] = pivot_value;
    array[pivot_index] = tmp;
  }

  //@ assert permut_double{Pre, Here}(array, array, l, h);

  size_t i = l;
  size_t store_index = l;

  /*@ loop invariant l <= i <= h;
    @ loop invariant l <= store_index <= i;
    @ loop invariant \valid(array+(l..h));
    @ loop invariant \forall integer k; l <= k < store_index ==> array[k] < pivot_value;
    @ loop invariant \forall integer k; store_index <= k < i ==> array[k] >= pivot_value;
    @ loop invariant array[h] == pivot_value;
    @ loop invariant permut_double{Pre, Here}(array, array, l, h);
    @ loop assigns array[l..h], store_index, i;
    @ loop variant (h - i);
  */

  while (i != h){

  L1:
    
    if (array[i] < pivot_value){

      double tmp = array[i];
      array[i] = array[store_index];
      array[store_index] = tmp;

      //@ assert (\forall integer k; l <= k <= h ==> k != i ==> k != store_index ==> \at(array[k], L1) == \at(array[k], Here));
      //@ assert \at(array[i], L1) == \at(array[store_index], Here) && \at(array[store_index], L1) == \at(array[i], Here);
      //@ assert permut_double{L1, Here}(array, array, l, h);

      ++ store_index;

    }

    ++i;
  }

  //@ assert permut_double{Pre, Here}(array, array, l, h);
  //@ assert l <= store_index <= h;
 L2: 
  {
    double tmp = array[h];
    array[h] = array[store_index];
    array[store_index] = tmp;

    //@ assert (\forall integer k; l <= k <= h ==> k != h ==> k != store_index ==> \at(array[k], L2) == \at(array[k], Here));
    //@ assert \at(array[h], L2) == \at(array[store_index], Here) && \at(array[store_index], L2) == \at(array[h], Here);
    //@ assert permut_double{L2, Here}(array, array, l, h);

  }


  return store_index;
}

void quicksort_double(double* array, const size_t l, const size_t h){
  
  if (l < h) {

    size_t p = partition_double(array, l, h);

    //@ assert \forall integer k; l <= k < p ==> array[k] < array[p];
    //@ assert \forall integer k; p <= k <= h  ==> array[p] <= array[k]; 

    if (l < p)
      quicksort_double(array, l, p-1);

    //@ assert \forall integer k; l <= k < p-1 ==> array[k] <= array[k+1];

    if (p < h)
      quicksort_double(array, p+1, h);

    //@ assert \forall integer k; p+1 <= k <= h ==> array[k] <= array[k+1];

  }
  
}
