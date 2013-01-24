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
// size: represent the type used to index into an array

// here we make the arbitrary choice of uint32_t, should be sufficient

typedef uint32_t size_t;


#endif
