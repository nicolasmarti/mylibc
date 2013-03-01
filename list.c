#include "list.h"

/*@ predicate is_circular_singly_list_loop_assert{L}(
  @ singly_list_t *lst, 
  @ singly_list_t *fast, 
  @ singly_list_t *slow, 
  @ int dist_lst_slow,
  @ int dist_slow_fast,
  @ integer dist) =
  @   fast != slow &&
  @   fast != \null &&
  @   slow != \null &&
  @   wf_singly_list(slow) &&
  @   wf_singly_list(fast) &&
  @   wf_singly_list(lst) &&
  @   \valid(fast) &&
  @   \valid(slow) &&
  @   reachable(lst, slow, dist_lst_slow) &&
  @   reachable(slow, fast, dist_slow_fast) &&
  @   reachable(lst, fast, dist_lst_slow + dist_slow_fast) &&
  @   dist_slow_fast > dist &&
  @   dist_lst_slow >= 0;      
*/


int is_circular_singly_list(singly_list_t* lst){

  singly_list_t *slow, *fast;
  unsigned int cpter;


  if (lst == 0) {
    //@ assert !circular_singly_list(lst);
    return 0;
  }

  //@ assert lst != \null;

  if (lst == lst->next){
    //@ assert reachable(lst, lst, 0) && reachable (lst, lst, 1);
    //@ assert circular_singly_list(lst);
    return 1;
  }

  if (lst->next == 0){
    //@ assert !circular_singly_list(lst);
    return 0;
  }

  // seems to be a known bug: http://bts.frama-c.com/view.php?id=387
  // this is a ticket from (2010-02-01 09:46) still not solved ...
  // a related message: http://stackoverflow.com/questions/9956173/acsl-set-logic-frama-c-syntax-error
  // and finally the frama-c-acsl-implementation manuel says that it is not supported
  // http://frama-c.com/download/frama-c-acsl-implementation.pdf
  // it will make the verification to fail on rte assert on both ghost variable
  //@ ghost int dist_slow_fast = 1;
  //@ ghost int dist_lst_slow = 0;

  slow = lst;
  fast = lst->next;

  /////////////////////////////////////////////////////////////////////////////////

  /*@ loop invariant is_circular_singly_list_loop_assert(lst, fast, slow, dist_lst_slow, dist_slow_fast, 0);
    @ loop assigns fast, slow, dist_slow_fast, dist_lst_slow;
  */
  while (1) {

    //@ assert is_circular_singly_list_loop_assert(lst, fast, slow, dist_lst_slow, dist_slow_fast, 0);

    // advance fast by one
    if (fast-> next == 0){
      //@ assert !circular_singly_list(lst);
      return 0;
    } else {
      fast = fast-> next;
      //@ ghost ++dist_slow_fast;
    }

    if (fast == slow){
      //@ assert circular_singly_list(lst);
      return 1;
    }
    
    //@ assert is_circular_singly_list_loop_assert(lst, fast, slow, dist_lst_slow, dist_slow_fast, 1);

    // advance fast by one
    if (fast-> next == 0){
      //@ assert !circular_singly_list(lst);
      return 0;
    } else {
      fast = fast-> next;
      //@ ghost ++dist_slow_fast;
    }

    if (fast == slow){
      //@ assert circular_singly_list(lst);
      return 1;
    }

    //@ assert is_circular_singly_list_loop_assert(lst, fast, slow, dist_lst_slow, dist_slow_fast, 2);

    // advance fast by one
    if (fast-> next == 0){
      //@ assert !circular_singly_list(lst);
      return 0;
    } else {
      fast = fast-> next;
      //@ ghost ++dist_slow_fast;
    }

    if (fast == slow){
      //@ assert circular_singly_list(lst);
      return 1;
    }

    //@ assert is_circular_singly_list_loop_assert(lst, fast, slow, dist_lst_slow, dist_slow_fast, 3);

    // advance slow by one
    slow = slow->next;
    //@ ghost ++dist_lst_slow;
    //@ ghost --dist_slow_fast;

    if (fast == slow){
      //@ assert circular_singly_list(lst);
      return 1;
    }

    //@ assert is_circular_singly_list_loop_assert(lst, fast, slow, dist_lst_slow, dist_slow_fast, 2);

  }
  /////////////////////////////////////////////////////////////////////////////////
  

}

