#ifndef STRING_H
#define STRING_H

///////////////////////////////////////////////////
// ascii encoding of strings

#include "basetype.h"

typedef uint8_t* string_t;

// here we just state as the invariant that a string is an valid array of char, containing at least one null character
// NB: we neither state that the last char is null, or that there is only one null char

// the size of a string
/*@ 
  predicate string_size(string_t s, size_t n) = \valid(s+(0..n-1)) && \exists size_t i; 0 <= i < n  && s[i] == 0 ;
 */

/*@ predicate wf_string(string_t s) = \exists size_t n; string_size(s, n); */


// not yet handled ... 
/*@ type invariant string_invariant(string_t s) = wf_string(s) ; */ 

///////////////////////////////////////////////////

/* usefull functions */


// the length of a string
/*@
  requires wf_string(s);
  assigns \nothing;  
  ensures \valid(s+(0..\result-1));
  ensures \forall size_t i; 0 <= i < \result ==> s[i] != 0;
  ensures s[\result] == 0;
 */

size_t my_strlen(const string_t s);

#endif
