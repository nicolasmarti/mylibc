#define value_type unsigned int

/////////////// Base definition

/*@
  @ logic integer occurence{L}( value_type* a, integer l, integer h, value_type e ) =
  @               l >= h ? 0 : ( a[l] == e ? 1 : 0 ) + occurence( a, l+1, h, e );
  @
*/

/////// Axioms with functions as proof

// range

/*@ requires l <= h;
  @ assigns \nothing;
  @ ensures 0 <= occurence( a, l, h, e ) <= h - l;
*/
void occurence_range_proof( value_type* a, unsigned int l, unsigned int h, value_type e ){

  /*@ loop invariant l <= i <= h;
    @ loop invariant 0 <= occurence( a, l, i, e ) <= i - l;
    @ loop assigns i;
    @ loop variant (h - i);
  */
  for (unsigned int i = l; i != h; ++i){}
  
}

/*@
  @ axiomatic Occurence_range {
  @
  @ axiom occurence_n_range: \forall value_type* a, integer l,  h, value_type e, integer n;
  @                           l <= h ==> 0 <= occurence( a, l, h, e ) <= h - l;
  @ }
  @
*/


// reverse

/*@ requires l < h;
  @ assigns \nothing;
  @ ensures occurence( a, l, h, e ) == (a[h-1] == e ? 1 : 0) + occurence( a, l, h-1, e);
*/
void occurence_reverse_proof( value_type* a, unsigned int l, unsigned int h, value_type e ){

  /*@ loop invariant l <= i < h;
    @ loop invariant occurence( a, i, h, e ) == (a[h-1] == e ? 1 : 0) + occurence( a, i, h-1, e);
    @ loop assigns i;
    @ loop variant (i - l);
  */
  for (unsigned int i = h-1; i != l; --i){}
  
}

/*@
  @ axiomatic Occurence_reverse {
  @
  @ axiom occurence_reverse: \forall value_type* a, integer l,  h, value_type e, integer n;
  @                           l < h ==> occurence( a, l, h, e ) == (a[h-1] == e ? 1 : 0) + occurence( a, l, h-1, e);
  @ }
  @
*/

// split



/*@ requires l <= cut <= h;
  @ assigns \nothing;
  @ ensures occurence( a, l, h, e ) == occurence( a, l, cut, e ) + occurence( a, cut, h, e );
*/
void occurence_split_proof( value_type* a, unsigned int l, unsigned int h, value_type e, unsigned int cut ){
  
  /*@ loop invariant cut <= i <= h;
    @ loop invariant occurence( a, l, i, e ) == occurence( a, l, cut, e ) + occurence( a, cut, i, e );
    @ loop assigns i;
    @ loop variant (h - i);
  */
  for (unsigned int i = cut; i != h; ++i){}
  
}

/*@
  @ axiomatic Occurence_split{
  @
  @ axiom occurence_split: \forall value_type* a, integer l,  h, value_type e, integer cut;
  @                        l <= cut <= h ==> occurence( a, l, h, e ) == occurence( a, l, cut, e ) + occurence( a, cut, h, e );   
  @ }
  @
*/


/////// a function computing the occurence

/*@ requires \valid( a+(l..h-1) );
  @ requires l < h;
  @ 
  @ assigns \nothing;
  @
  @ ensures \result == occurence( a, l, h, e );
*/



unsigned int occurence( value_type* a, unsigned int l, unsigned int h, value_type e ){

  unsigned int result = 0;

  /*@ loop invariant occurence_i_range: l <= i <= h;
    @ loop invariant always_valid: \valid( a+(l..h-1) );
    @ loop invariant occurence_result_prefix: occurence( a, l, h, e ) == result + occurence( a, i, h, e );
    @ loop assigns i, result;
    @ loop variant (h - i);
  */
  for (unsigned int i = l; i != h; ++i){
    
    if (a[i] == e)
      result += 1;
    
  }

  return result;
  
}

////// permutation definition

/*@
  @ predicate permutation{L1, L2}( value_type* a, integer l, integer h ) = 
  @           \forall value_type e; occurence{L1}( a, l, h, e ) == occurence{L2}( a, l, h, e );
*/

/// swap

/*@
  @ requires l <= i1 < h;
  @ requires l <= i2 < h;
  @ requires \valid( a+(l..h-1) );
  @
  @ assigns a[i1], a[i2];
  @
  @ ensures \at( a[i1], Post ) == \at( a[i2], Pre );
  @ ensures \at( a[i2], Post ) == \at( a[i1], Pre );
  @ ensures permutation{ Pre, Post }( a, l, h );
*/
void swap( value_type* a, unsigned int l, unsigned int h, unsigned int i1, unsigned int i2 ){

  value_type tmp = a[i2];
  /*@ghost occurence_split_proof( a, l, h, a[i2], i2 ); */
  //@assert A1: occurence( a, l, i2, a[i2] ) == occurence( a, l, i2, a[i2] ) + occurence( a, i2, h, a[i2] );
  a[i2] = a[i1];
  a[i1] = tmp;

}

/*@ predicate ordered( value_type* a, integer l, integer h ) =
  @           \forall integer k1, k2; l <= k1 <= k2 < h ==> a[k1] <= a[k2];
*/

/*@ requires \valid( a+(l..h-1) );
  @ requires l < h;
  @
  @ assigns a[l..h-1];
  @
  @ ensures l <= \result < h;
  @ ensures \forall integer k; l <= k <= \result ==> a[k] <= a[\result];
  @ ensures \forall integer k; \result <= k < h  ==> a[\result] <= a[k];
  @ ensures permutation{Pre, Post}( a, l, h );
*/
unsigned int partition( value_type* a, unsigned int l, unsigned int h ){

  const unsigned int pivot_index = l + (h - l)/2;

  const value_type pivot_value = a[pivot_index];

  swap( a, l, h, pivot_index, h-1 );

  unsigned int store_index = l;
  
  /*@ loop invariant i_range: l <= i <= h;
    @ loop invariant store_index_rage: l <= store_index <= i;
    @ loop invariant lt_pivot: \forall integer k; l <= k < store_index ==> a[k] < pivot_value;
    @ loop invariant geq_pivot: \forall integer k; store_index <= k < i ==> a[k] >= pivot_value;
    @ loop invariant pivot_value_inv: a[h] == pivot_value;
    @ loop invariant is_permut: permutation{Pre, Here}(a, l, h);
    @ loop assigns a[l..h-1], store_index, i;
    @ loop variant (h - i);
  */
  for (unsigned int i = l; i != h; ++i){

    if (a[i] < pivot_value){
      swap( a, l, h, i, store_index );
      ++store_index;
    }

  }

  swap( a, l, h, store_index, h-1 );

  return store_index;
  

  
}

/*@ requires \valid( a+(l..h-1) );
  @ requires l < h;
  @
  @ assigns a[l..h-1];
  @
  @ ensures ordered( a, l, h );
  @ ensures permutation{Pre, Post}( a, l, h );
*/
void qsort( value_type* a, unsigned int l, unsigned int h ){

  unsigned int p = partition( a, l, h );

  if (l < p)
    qsort( a, l, p );

  if(p < h-1)
    qsort( a, p+1, h );

  return;

}


