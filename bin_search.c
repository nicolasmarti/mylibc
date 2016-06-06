#include "bin_search.h"

size_t bin_search( double* array, size_t l, size_t h, double v){

  size_t low = l;
  size_t high = h-1;

  if (v < array[l])
    return h;

  if (array[high] < v)
    return h;

  /*@ loop invariant l <= low;
    @ loop invariant high < h;
    @ loop invariant !contains{Pre}(array, l, low-1, v);
    @ loop invariant !contains{Pre}(array, high+1, h-1, v);
    @ loop invariant ordered_array_double(array, low, high);
    @ loop invariant \valid(array+(low..high));
    @ loop assigns high, low;
    @ loop variant (high - low);
  */

  while (low <= high){

    size_t mid = low + (high - low) / 2;
    //@ assert low <= mid <= high;

    if (array[mid] == v)
      return mid;

    if (array[mid] < v)
      low = mid+1;

    if (v < array[mid])
      high = mid-1;

  }

  return h;

}
