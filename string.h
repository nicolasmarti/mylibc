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
  predicate string_size(string_t s, size_t n) = \valid(s+(0..n)) && \exists size_t i; 0 <= i <= n  && s[i] == 0 ;
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

// compare two string
/*@

  requires wf_string(s2);

  assigns \nothing;  

  behavior lt:
    assumes \forall size_t sz1; string_size(s1, sz1) ==>
            \forall size_t sz2; string_size(s2, sz2) ==>
                 \exists index_t i;
		 0 <= i <= sz1 && 0 <= i <= sz2 &&
		    (\forall index_t j; 0 <= j < i ==> s1[j] == s2[j]) &&
		    s1[i] < s2[i];

    ensures \result == Lt;

  behavior gt:
    assumes \forall size_t sz1; string_size(s1, sz1) ==>
            \forall size_t sz2; string_size(s2, sz2) ==>
                 \exists index_t i;
		 0 <= i <= sz1 && 0 <= i <= sz2 &&
		    (\forall index_t j; 0 <= j < i ==> s1[j] == s2[j]) &&
		    s1[i] > s2[i];

    ensures \result == Gt;

  behavior eq:

    assumes \forall size_t sz1; string_size(s1, sz1) ==>
            \forall size_t sz2; string_size(s2, sz2) ==>
	    sz1 == sz2 &&
	    \forall index_t i; 0 <= i < sz1 ==> s1[i] == s2[i];

    ensures \result == Eq;

  complete behaviors;
  disjoint behaviors;

 */

cmp_t my_strcmp(const string_t s1, const string_t s2);


#endif
