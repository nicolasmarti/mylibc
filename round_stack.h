#ifndef ROUND_STACK_H
#define ROUND_STACK_H

#include "basetype.h"

// the round_stack_header

typedef struct {

  // size of element in byte
  size_t element_size;

  // number of element that can be stored
  size_t nb_storable_element;

  // number of element actually stored
  size_t nb_stored_element;

  // start,end slots
  index_t start_slot, current_slot;

  // the storage
  any_ptr_t storage;

} round_stack_t;


/*@
  @predicate wf_round_stack(round_stack_t st) = 
  @  // validity of the storage  
  @  \valid(st.storage+(0..st.element_size*st.nb_storable_element)) &&
  @  // validity ranges for start / current pointer
  @  0 <= st.start_slot < st.nb_storable_element &&  
  @  0 <= st.current_slot < st.nb_storable_element &&
  @  // link between start/current slots pointers and nb_stored_elements
  @  (st.start_slot == st.current_slot ==> (st.nb_stored_element == st.nb_storable_element || st.nb_stored_element == 0)) &&  
  @  (st.start_slot < st.current_slot ==> st.nb_stored_element == st.current_slot - st.start_slot) &&
  @  (st.start_slot > st.current_slot ==> st.nb_stored_element == st.nb_storable_element - (st.start_slot - st.current_slot));     
 */

// not yet handled ... 
/*@ type invariant round_stack_invariant(round_stack_t s) = wf_round_stack(s) ; */ 

////////////////////////////////////////////////////////////////////////////////////
// initialize function

// it takes a pointer to a round_stack header, build the storage and sets the nb_stored_element, start_slot, current_slot and storage fields
// returns 0 if failed, and 1 if succeed

/*@
  @requires \valid(\base_addr(s)+(0..\block_length(s)-1));
  @requires \valid(s);
  @//@requires s->element_size*s->nb_storable_element < \offset_max(s->storage);
  @allocates(s->storage);
  @behavior failed:
  @   assigns s->storage;
  @   ensures \result == 0;
  @   ensures s->storage == \null;
  @behavior succeed:
  @  assigns s->nb_stored_element, s->start_slot, s->current_slot, s->storage;
  @  ensures \result == 1;
  @  ensures s->start_slot == 0;
  @  ensures s->current_slot == 0;
  @  ensures s->nb_stored_element == 0;
  @  ensures wf_round_stack(*s);
  @  ensures \separated(s, s->storage);
  @  
  @  complete behaviors;
  @  disjoint behaviors;
 */

uint8_t init_round_stack(round_stack_t *s);

////////////////////////////////////////////////////////////////////////////////////
// pushing on the stack

// returns 0 if failed, and 1 if succeed

/*@ // definition of a full roundstack
  @ predicate round_stack_full(round_stack_t s) =
  @   s.start_slot == s.current_slot && s.nb_stored_element == s.nb_storable_element;
  @
  @// definition of an empty roundstack
  @ predicate round_stack_empty(round_stack_t s) =
  @   s.start_slot == s.current_slot && s.nb_stored_element == 0;
  @*/


/*@
  @requires \valid(\base_addr(s)+(0..\block_length(s)-1));
  @requires \valid(s);
  @requires \valid(elt+(0..s->element_size-1));
  @requires wf_round_stack(*s);
  @
  @ensures wf_round_stack(*s);
  @
  @behavior failed:
  @  assumes round_stack_full(*s);
  @  assigns \nothing;
  @  ensures \result == 0;
  @  
  @behavior succeed:
  @  assumes !round_stack_full(*s);
  @  assigns s->nb_stored_element, s->current_slot, s->storage[(s->current_slot*s->element_size)..((s->current_slot+1)*s->element_size - 1)];
  @  ensures s->storage[(s->current_slot*s->element_size)..((s->current_slot+1)*s->element_size - 1)] == elt[0..s->element_size-1];
  @  ensures s->nb_stored_element == \old(s->nb_stored_element) + 1;
  @  ensures \result == 1;
  @  
  @
  @complete behaviors;
  @disjoint behaviors;
  @*/

uint8_t round_stack_push(round_stack_t* s, any_ptr_t elt);

#endif
