#include "basetype.h"

cmp_t uint8_cmp(const uint8_t i1, const uint8_t i2){

  if (i1 == i2)
    return Eq;

  if (i1 < i2)
    return Lt;

  return Gt;

}
