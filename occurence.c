#define value_type double

/*@
  @ predicate occurence1( value_type* a, integer l, integer h, value_type e, integer n ) = ( l >= h ==> n == 0 ) || ( l < h ==> occurence1( a, l+1, h, e, ( a[l] == e ? n-1 : n ) ) );
  @
  @
  @ axiomatic Occurence1 {
  @
  @ axiom occurence1_n_uniq: \forall value_type* a, integer l,  h, value_type e, integer n1, n2;
  @       occurence1( a, l, h, e, n1 ) ==>
  @       occurence1( a, l, h, e, n2 ) ==>
  @       n1 == n2;
  @
  @ axiom occurence1_n_exists: \forall value_type* a, integer l,  h, value_type e;
  @                            \exists integer n; occurence1( a, l, h, e, n );
  @
  @ axiom occurence1_n_range: \forall value_type* a, integer l,  h, value_type e, integer n;
  @                           occurence1( a, l, h, e, n ) ==>
  @                           0 <= n <= h - l;
  @ }
  @
*/

/*@ requires \valid( a+(l..h-1) );
  @ requires l < h;
  @ 
  @ assigns \nothing;
  @
  @ ensures occurence1( a, l, h, e, \result );
*/

unsigned int f1( value_type* a, unsigned int l, unsigned int h, value_type e ){

  unsigned int result = 0;

  unsigned int i = l;

  /*@ loop invariant i_range: l <= i <= h;
    @ loop invariant result_prefix: \forall unsigned int n, n_i;
    @                                       occurence1( a, l, h, e, n ) ==>
    @                                       occurence1( a, i, h, e, n_i ) ==>
    @                                       n == result + n_i;
    @ loop assigns i, result;
    @ loop variant (h - i);
  */
  while (i < h){

    if (a[i] == e)
      result += 1;

    i += 1;
    
  }

  return result;
  
}


/*@
  @ inductive occurence2( value_type* a, integer l, integer h, value_type e, integer n ){
  @ 
  @ case no_more_element: \forall value_type* a, integer l,  h, value_type e;
  @                       l >= h ==> occurence2( a, l, h, e, 0 );
  @
  @ case no_match: \forall value_type* a, integer l,  h, value_type e, integer n;
  @                       l < h ==> 
  @                       a[l] != e ==>
  @                       occurence2( a, l+1, h, e, n ) ==>
  @                       occurence2( a, l, h, e, n );
  @
  @ case match: \forall value_type* a, integer l,  h, value_type e, integer n;
  @                       l < h ==> 
  @                       a[l] == e ==>
  @                       occurence2( a, l+1, h, e, n-1 ) ==>
  @                       occurence2( a, l, h, e, n );  
  @
  @ }
  @
  @
  @ axiomatic Occurence2 {
  @
  @ axiom occurence2_n_uniq: \forall value_type* a, integer l,  h, value_type e, integer n1, n2;
  @       occurence2( a, l, h, e, n1 ) ==>
  @       occurence2( a, l, h, e, n2 ) ==>
  @       n1 == n2;
  @
  @ axiom occurence2_n_exists: \forall value_type* a, integer l,  h, value_type e;
  @                            \exists integer n; occurence2( a, l, h, e, n );
  @
  @ axiom occurence2_n_range: \forall value_type* a, integer l,  h, value_type e, integer n;
  @                           occurence2( a, l, h, e, n ) ==>
  @                           0 <= n <= h - l;
  @ }
  @
*/

/*@ requires \valid( a+(l..h-1) );
  @ requires l < h;
  @ 
  @ assigns \nothing;
  @
  @ ensures occurence2( a, l, h, e, \result );
*/

unsigned int f2( value_type* a, unsigned int l, unsigned int h, value_type e ){

  unsigned int result = 0;

  unsigned int i = l;

  /*@ loop invariant i_range: l <= i <= h;
    @ loop invariant result_prefix: \forall unsigned int n, n_i;
    @                                       occurence2( a, l, h, e, n ) ==>
    @                                       occurence2( a, i, h, e, n_i ) ==>
    @                                       n == result + n_i;
    @ loop assigns i, result;
    @ loop variant (h - i);
  */
  while (i < h){

    if (a[i] == e)
      result += 1;

    i += 1;
    
  }

  return result;
  
}


/*@
  @ logic integer occurence3( value_type* a, integer l, integer h, value_type e ) =
  @               l >= h ? 0 : ( a[l] == e ? 1 : 0 ) + occurence3( a, l+1, h, e );
  @
  @
  @ axiomatic Occurence3 {
  @
  @ axiom occurence3_n_range: \forall value_type* a, integer l,  h, value_type e, integer n;
  @                           0 <= occurence3( a, l, h, e ) <= h - l;
  @ }
  @
*/

/*@ requires \valid( a+(l..h-1) );
  @ requires l < h;
  @ 
  @ assigns \nothing;
  @
  @ ensures \result == occurence3( a, l, h, e );
*/

unsigned int f3( value_type* a, unsigned int l, unsigned int h, value_type e ){

  unsigned int result = 0;

  unsigned int i = l;

  /*@ loop invariant i_range: l <= i <= h;
    @ loop invariant result_prefix: occurence3( a, l, h, e ) == result + occurence3( a, i, h, e );
    @
    @ loop assigns i, result;
    @ loop variant (h - i);
  */
  while (i < h){

    if (a[i] == e)
      result += 1;

    i += 1;
    
  }

  return result;
  
}
