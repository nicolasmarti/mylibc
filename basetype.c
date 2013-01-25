#include "basetype.h"

cmp_t uint8_cmp(const uint8_t i1, const uint8_t i2){

  if (i1 == i2)
    return Eq;

  if (i1 < i2)
    return Lt;

  return Gt;

}


cmp_t sint8_cmp(const sint8_t i1, const sint8_t i2){

  if (i1 == i2)
    return Eq;

  if (i1 < i2)
    return Lt;

  return Gt;

}


cmp_t uint16_cmp(const uint16_t i1, const uint16_t i2){

  if (i1 == i2)
    return Eq;

  if (i1 < i2)
    return Lt;

  return Gt;

}


cmp_t sint16_cmp(const sint16_t i1, const sint16_t i2){

  if (i1 == i2)
    return Eq;

  if (i1 < i2)
    return Lt;

  return Gt;

}


cmp_t uint32_cmp(const uint32_t i1, const uint32_t i2){

  if (i1 == i2)
    return Eq;

  if (i1 < i2)
    return Lt;

  return Gt;

}


cmp_t sint32_cmp(const sint32_t i1, const sint32_t i2){

  if (i1 == i2)
    return Eq;

  if (i1 < i2)
    return Lt;

  return Gt;

}


cmp_t uint64_cmp(const uint64_t i1, const uint64_t i2){

  if (i1 == i2)
    return Eq;

  if (i1 < i2)
    return Lt;

  return Gt;

}


cmp_t sint64_cmp(const sint64_t i1, const sint64_t i2){

  if (i1 == i2)
    return Eq;

  if (i1 < i2)
    return Lt;

  return Gt;

}
