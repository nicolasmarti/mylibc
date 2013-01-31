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
  index_t start_slot, stop_slot;

  // the storage
  char* storage;

} round_stack_t;


/*@
  @predicate wf_round_stack(round_stack_t st) = 
  @  // validity of the storage  
  @  \valid(st.storage+(0..st.element_size*st.nb_storable_element)) &&
  @  // validity ranges for start / stop pointer
  @  0 <= st.start_slot < st.nb_storable_element &&  
  @  0 <= st.stop_slot < st.nb_storable_element &&
  @  // link between start/stop slots pointers and nb_stored_elements
  @  (st.start_slot == st.stop_slot ==> (st.nb_stored_element == st.nb_storable_element || st.nb_stored_element == 0)) &&  
  @  (st.start_slot < st.stop_slot ==> st.nb_stored_element == st.stop_slot - st.start_slot) &&
  @  (st.start_slot > st.stop_slot ==> st.nb_stored_element == st.nb_storable_element - (st.start_slot - st.stop_slot));     
 */

// not yet handled ... 
/*@ type invariant round_stack_invariant(round_stack_t s) = wf_round_stack(s) ; */ 

// initialize function
// it takes a pointer to a round_stack header, build the storage and sets the nb_stored_element, start_slot, stop_slot and storage fields
// returns 0 if failed, and 1 if succeed

/*@
  @requires \valid(\base_addr(s)+(0..\block_length(s)-1));
  @requires \valid(s);
  @//@requires s->element_size*s->nb_storable_element < \offset_max(s->storage);
  @behavior failed:
  @   assigns s->storage;
  @   ensures \result == 0;
  @   ensures s->storage == \null;
  @behavior succeed:
  @  assigns s->nb_stored_element, s->start_slot, s->stop_slot, s->storage;
  @  ensures \result == 1;
  @  ensures s->start_slot == 0;
  @  ensures s->stop_slot == 0;
  @  ensures s->nb_stored_element == 0;
  @  ensures wf_round_stack(*s);
  @  ensures \separated(s, s->storage);
  @  allocates(s->storage);
 */

uint8_t init_round_stack(round_stack_t *s);

#endif
