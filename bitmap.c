#include "bitmap.h"


uint_t cell_log_pow2(size_t x, uint_t y){

  uint_t res = 1;

  /*@

    loop assigns x, res;
    loop invariant pow(pow2(y), (res -1) + x) <= \at(x, Pre) <= pow(pow2(y), res + x);

  */

  while (x >>= y)
    {
      res++;
    }

  return res;

}

