
// compare two string
// will do that later:
//  complete behaviors;
//  disjoint behaviors;

/*@

  requires wf_string(s1);
  requires wf_string(s2);

  assigns \nothing;  

  behavior lt:
    assumes \forall size_t sz1; string_size(s1, sz1) ==>
            \forall size_t sz2; string_size(s2, sz2) ==>
                 \exists index_t i;
		 0 <= i <= sz1 && 0 <= i <= sz2 &&
		    (\forall index_t j; 0 <= j < i ==> s1[j] == s2[j]) &&
		    s1[i] < s2[i];

    ensures \result == Lt;

  behavior gt:
    assumes \forall size_t sz1; string_size(s1, sz1) ==>
            \forall size_t sz2; string_size(s2, sz2) ==>
                 \exists index_t i;
		 0 <= i <= sz1 && 0 <= i <= sz2 &&
		    (\forall index_t j; 0 <= j < i ==> s1[j] == s2[j]) &&
		    s1[i] > s2[i];

    ensures \result == Gt;

  behavior eq:

    assumes \forall size_t sz1; string_size(s1, sz1) ==>
            \forall size_t sz2; string_size(s2, sz2) ==>
	    sz1 == sz2 &&
	    \forall index_t i; 0 <= i < sz1 ==> s1[i] == s2[i];

    ensures \result == Eq;


 */

cmp_t my_strcmp(const string_t s1, const string_t s2);


cmp_t my_strcmp(const string_t s1, const string_t s2){

  index_t counter = 0;

  /*@
    loop invariant 
       \forall size_t sz1; string_size(s1, sz1) ==>
       \forall size_t sz2; string_size(s2, sz2) ==>
       counter <= sz1 && counter <= sz2;
    loop assigns counter;
   */
  for (counter = 0; ; ++counter)
    {

      switch (uint8_cmp(s1[counter], s2[counter])){

      case Eq:
	if (s1[counter] == 0)
	  return Eq;
	break;

      case Lt:
	return Lt;
	
      case Gt:
	return Gt;

      }

      
    }

}


/*@     
  lemma str_cmp_complete: \forall string_t s1; \forall string_t s2;
     (wf_string(s1) && wf_string(s2)) ==> str_lt(s1, s2) || str_eq(s1, s2) || str_gt(s1, s2);
*/