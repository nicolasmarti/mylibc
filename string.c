#include "string.h"

size_t my_strlen(const string_t s){

  index_t counter = 0;

  /*@
    loop invariant \forall size_t j ; 0 <= j < counter ==> s[j] != 0;
    loop assigns counter;
    
    
   */
  for (counter = 0; s[counter] != 0; ++counter){
  }

  return counter;

}


cmp_t my_strcmp(const string_t s1, const string_t s2){

  index_t counter = 0;

  /*@
    loop invariant 
       \forall size_t sz1; string_size(s1, sz1) ==>
       \forall size_t sz2; string_size(s2, sz2) ==>
       counter <= sz1 && counter <= sz2 &&
       (\forall index_t i; 0 <= i < counter ==> s1[i] == s2[i]);
    loop assigns counter;
   */
  for (counter = 0; ; counter++)
    {

      switch (uint8_cmp(s1[counter], s2[counter])){

      case Eq:
	if (s1[counter] == 0 && s2[counter] == 0){
	  return Eq;
	}
	break;

      case Lt:
	return Lt;
	
      case Gt:
	return Gt;

      }

      
    }

}

