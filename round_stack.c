#include "round_stack.h"
#include <stdlib.h>

uint8_t init_round_stack(round_stack_t *s){

  if (0 == (s->storage = (char*)(malloc(s->element_size * s->nb_storable_element))))
    return 0;

  s->start_slot = s->stop_slot = s->nb_storable_element = 0;
  
  return 1;

}
