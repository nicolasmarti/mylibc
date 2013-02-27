
typedef struct _list {
  double elt;
  struct _list* next;
} list_t;

/*@
  @ inductive wf_list{L}(list_t* l) {
  @ case empty: \forall list_t* l; l == \null ==> wf_list(l);
  @ case non_empty: \forall list_t* l; l != \null ==> \valid(l) ==> wf_list(l->next) ==> wf_list(l);
  @ }
  @ 
  @ axiomatic wf_list {
  @ axiom wf_list_inversion: \forall list_t* l; wf_list(l) ==>
  @ l == \null || (l != \null && \valid(l) && wf_list(l->next));
  @ }
  @
*/

/*@
  @ inductive reachable{L}(list_t* l1, list_t* l2, integer n) {
  @ case empty: \forall list_t* l; reachable(l, l, 0);
  @ case non_empty: \forall list_t *l1, *l2; \forall integer n; l1 != \null ==> \valid(l1) ==> reachable(l1->next, l2, n) ==> reachable(l1, l2, n + 1);
  @ }
  @ 
  @ lemma reachable_geq0: \forall list_t *l1, *l2; \forall integer n; reachable(l1, l2, n) ==> n >= 0;
  @
*/
