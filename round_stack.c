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
  if (s->nb_stored_element != s->nb_storable_element){
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

int round_stack_pop(round_stack_t* s, any_ptr_t elt){

  // look if the stack is empty
  if (s->nb_stored_element != 0){
    // no: we can pop
    
    // copying the element
    memcpy(elt, s->storage + s->current_slot * s->element_size, s->element_size);

    // update the fields and return the result
    if (s->current_slot == 0)
      s->current_slot = s->nb_storable_element - 1;
    else
      --s->current_slot;
    
    --s->nb_stored_element;
        
    return 1;

  } else {
    // yes: return fail
    return 0;
  }

}

uint8_t round_stack_insert_first(round_stack_t* s, any_ptr_t elt){

// looking if the stack is full or not
  if (s->nb_stored_element != s->nb_storable_element){
    // not full, do the insertion
   
    // we decr the start_slot
    if (s->start_slot == 0)
      s->start_slot = s->nb_storable_element - 1;
    else
      --s->start_slot;
 
    // getting the place were to put the element
    any_ptr_t storage = s->storage + s->element_size * s->start_slot;
    
    // and copying it
    memcpy(storage, elt, s->element_size);
    
    // updates stack fields: current_slot and nb_stored_element
    s->nb_stored_element++;
    
    // return succeed
    return 1;

  } else {
    // full: return failed
    return 0;

  }

}


uint8_t round_stack_extract_first(round_stack_t* s, any_ptr_t elt){

  // look if the stack is empty
  if (s->nb_stored_element != 0){
    // no: we can pop
    
    // copying the element
    memcpy(elt, s->storage + s->start_slot * s->element_size, s->element_size);

    // update the fields and return the result
    s->start_slot = (s->start_slot + 1) % s->nb_storable_element;    
    --s->nb_stored_element;
        
    return 1;

  } else {
    // yes: return fail
    return 0;
  }

}
