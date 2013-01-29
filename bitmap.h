#ifndef BITMAP_H
#define BITMAP_H

#include "basetype.h"

#define UINT_SIZE_BIT sizeof(uint_t) * 8

// the definition of a bitmap
typedef uint_t* bitmap_t;

// pow on integer -> needs to be sure that y >= 0 for lemmas

// compute x power y

/*@
  logic integer pow(integer x, integer y) = y == 0 ? 1 : x * pow(x, y - 1);
 */

// compute 2 power x

/*@
  logic integer pow2(integer x) = pow(2, x);
 */


// compute the cell(log(x)/log(2^y))

/*@
  
  requires 0 <= y < 32;
  assigns \nothing;

  ensures pow(pow2(y), \result - 1) <= \old(x) <= pow(pow2(y), \result);

 */ 

uint_t cell_log_pow2(size_t x, uint_t y);


#endif
