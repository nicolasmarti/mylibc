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

// definition/lemma about the minimum of size_t
/*
  logic size_t size_min(size_t s1, size_t s2) = s1 < s2 ? s1 : s2;

  lemma size_min_sem: \forall size_t s1, s2; size_min(s1, s2) <= s1 && size_min(s1, s2) <= s2 && (size_min(s1, s2) == s1 || size_min(s1, s2) == s2);

 */

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

cmp_t sint8_cmp(const sint8_t i1, const sint8_t i2);

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

cmp_t uint16_cmp(const uint16_t i1, const uint16_t i2);

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

cmp_t sint16_cmp(const sint16_t i1, const sint16_t i2);


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

cmp_t uint32_cmp(const uint32_t i1, const uint32_t i2);

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

cmp_t sint32_cmp(const sint32_t i1, const sint32_t i2);


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

cmp_t uint64_cmp(const uint64_t i1, const uint64_t i2);

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

cmp_t sint64_cmp(const sint64_t i1, const sint64_t i2);


////////////////////////////////////////////////
// bool

typedef enum {True, False} bool_t;

#endif
