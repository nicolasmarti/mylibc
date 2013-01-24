#ifndef BASETYPE_H
#define BASETYPE_H

// this is just renaming for types

/////////////////////////////////////////////////
// integers
// format [s|u]int[<size in bits>]_t

typedef signed char sint8_t;
typedef unsigned char uint8_t;
typedef short sint16_t;
typedef unsigned short uint16_t;
typedef long sint32_t;
typedef unsigned long uint32_t;
typedef long long sint64_t;
typedef unsigned long long uint64_t;

////////////////////////////////////////////////
// the types used for size and to index into an array

// here we make the arbitrary choice of uint32_t, should be sufficient

typedef uint32_t size_t;
typedef uint32_t index_t;

////////////////////////////////////////////////
// comparaison

typedef enum {Lt, Eq, Gt} cmp_t;

/*@
  assigns \nothing;
  
  behavior lt:
    assumes i1 < i2;
    ensures \result == Lt;

  behavior eq:
    assumes i1 == i2;
    ensures \result == Eq;

  behavior gt:
    assumes i1 > i2;
    ensures \result == Gt;

  complete behaviors;
  disjoint behaviors;

*/

cmp_t uint8_cmp(const uint8_t i1, const uint8_t i2);

////////////////////////////////////////////////
// bool

typedef enum {True, False} bool_t;

#endif
