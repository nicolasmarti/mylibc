#ifndef BIN_SEARCH_H
#define BIN_SEARCH_H

#include <stddef.h>
#include "basetype.h"
#include "array_double.h"

/*@ requires \valid(array+(l..(h-1)));
  @ requires l < h;
  @ requires ordered_array_double(array, l, h-1);
  @ 
  @ assigns \nothing;
  @ 
  @ behavior failed:
  @    assumes !contains{Pre}(array, l, h-1, v);
  @    ensures \result == h;
  @
  @ behavior suceed:
  @   assumes contains{Pre}(array, l, h-1, v);
  @   ensures array[\result] == v;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
size_t bin_search( double* array, size_t l, size_t h, double v);


#endif
