#include "string.h"

size_t my_strlen(const string_t s){

  size_t counter = 0;

  /*@
    loop invariant \forall size_t j ; 0 <= j < counter ==> s[j] != 0;
    loop assigns counter;
    
    
   */
  for (counter = 0; s[counter] != 0; ++counter)
    {}

  return counter;

}
