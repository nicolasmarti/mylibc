#include "bitmap.h"


uint_t cell_log_pow2(size_t x, uint_t y){

  uint_t res = 1;

 Old:

  /*@
    loop assigns x, res;
    
  */

  while (x >>= y)
    {
      res++;
    }

  return res;

}

