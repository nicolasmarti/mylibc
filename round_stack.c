#include "round_stack.h"
#include <stdlib.h>
#include <string.h>

uint8_t init_round_stack(round_stack_t *s){

  // try to allocate, and if it fails return failed
  if (0 == (s->storage = (any_ptr_t)(malloc(s->element_size * s->nb_storable_element))))
    return 0;

  // else just set the structures fields and return succeed
  s->start_slot = s->current_slot = s->nb_storable_element = 0;
  
  return 1;

}

uint8_t round_stack_push(round_stack_t* s, any_ptr_t elt){

  // looking if the stack is full or not
  if (s->start_slot != s->current_slot || s->nb_stored_element == 0){
    // not full, do the insertion
    
    // getting the place were to put the element
    any_ptr_t storage = s->storage + s->element_size * s->current_slot;
    
    // and copying it
    memcpy(storage, elt, s->element_size);
    
    // updates stack fields: current_slot and nb_stored_element
    s->current_slot = (s->current_slot + 1) % s->nb_storable_element;
    s->nb_stored_element++;
    
    // return succeed
    return 1;

  } else {
    // full: return failed
    return 0;

  }

}
