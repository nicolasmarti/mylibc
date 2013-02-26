
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
  @ axiom empty{L}: \forall list_t* l; l == \null ==> wf_list(l);
  @ axiom non_empty{L}: \forall list_t* l; l != \null ==> \valid(l) ==> wf_list(l->next) ==> wf_list(l);
  @ axiom wf_list_inversion{L}: \forall list_t* l; wf_list(l) ==>
  @ l == \null || (l != \null && \valid(l) && wf_list(l->next));
  @ }
  @
*/
