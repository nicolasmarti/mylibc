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
    loop assigns counter;
   */
  for (counter = 0; ; ++counter)
    {

      switch (uint8_cmp(s1[counter], s2[counter])){

      case Eq:
	break;

      case Lt:
	return Lt;
	
      case Gt:
	return Gt;

      }

      
    }

}
