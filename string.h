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
  predicate string_size(string_t s, size_t n) = \valid(s+(0..n)) && (\forall size_t i; 0 <= i < n ==> s[i] != 0) && s[n] == 0 ;

  lemma string_size_uniq: \forall string_t s; 
                          \forall size_t n1, n2; 
			  string_size(s, n1) ==> string_size(s, n2) ==>
			  n1 == n2;

 */

/*@ predicate wf_string(string_t s) = \exists size_t n; string_size(s, n); */


// not yet handled ... 
/*@ type invariant string_invariant(string_t s) = wf_string(s) ; */ 

///////////////////////////////////////////////////

/* usefull functions */

//------------------------------------------------

// the length of a string
/*@
  requires wf_string(s);
  assigns \nothing;  
  ensures \valid(s+(0..\result));
  ensures \forall size_t i; 0 <= i < \result ==> s[i] != 0;
  ensures s[\result] == 0;
 */

size_t my_strlen(const string_t s);

//------------------------------------------------

// comparison between string
/*@
  
  predicate string_eq(string_t s1, string_t s2) = \exists size_t sz;
     string_size(s1, sz) && string_size(s2, sz) &&
     \forall index_t i; 0 <= i <= sz ==> s1[i] == s2[i];

  predicate string_lt(string_t s1, string_t s2) = \exists size_t sz1; \exists size_t sz2;
     string_size(s1, sz1) && string_size(s2, sz2) &&
     \exists index_t i; 0 <= i <= \min(sz1, sz2) &&
       (\forall index_t j; s1[j] == s2[j]) &&
       s1[i] < s2[i];

  predicate string_gt(string_t s1, string_t s2) = \exists size_t sz1; \exists size_t sz2;
     string_size(s1, sz1) && string_size(s2, sz2) &&
     \exists index_t i; 0 <= i <= \min(sz1, sz2) &&
       (\forall index_t j; s1[j] == s2[j]) &&
       s1[i] > s2[i];

  lemma l1: \forall string_t s1; \forall string_t s2;
     string_eq(s1, s2) ==> !string_lt(s1, s2) && !string_gt(s1, s2);

  lemma l2: \forall string_t s1; \forall string_t s2;
     string_lt(s1, s2) ==> !string_eq(s1, s2) && !string_gt(s1, s2);

  lemma l3: \forall string_t s1; \forall string_t s2;
     string_gt(s1, s2) ==> !string_eq(s1, s2) && !string_lt(s1, s2);

 */


// compare two string
// will do that later:
//  complete behaviors;
//  disjoint behaviors;

/*@

  requires wf_string(s1);
  requires wf_string(s2);

  assigns \nothing;  

  behavior lt:
    assumes string_lt(s1, s2);

    ensures \result == Lt;

  behavior gt:
    assumes string_gt(s1,s2);

    ensures \result == Gt;

  behavior eq:

    assumes string_eq(s1,s2);

    ensures \result == Eq;


 */

cmp_t my_strcmp(const string_t s1, const string_t s2);

#endif
