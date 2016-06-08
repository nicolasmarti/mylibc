
/*@ logic integer array_int_sum{L}(int *array, integer n) = (n < 0) ? 0 : (array[n] + array_int_sum(array, n-1));
  @
  @ axiomatic array_int_sum_extra {
  @
  @ axiom array_int_sum_invariant{L1, L2}:
  @  \forall int* a, integer n;
  @  (\forall integer k; 0 <= k < n ==> \at(a[k], L1) == \at(a[k], L2)) ==>
  @  array_int_sum{L1}(a, n) == array_int_sum{L2}(a, n);
  @
  @ }
*/

/*@ requires \valid(a+(0..(N-1)));
  @ requires N > 0;
  @ requires \valid(max);
  @ requires \valid(sum);
  @ requires \separated(max, sum, a+(0..(N-1)));
  @
  @ assigns *sum, *max;
  @
  @ ensures \forall integer k; 0 <= k < N ==> a[k] <= *max;
  @ ensures \exists integer k; 0 <= k < N && a[k] == *max;
  @ ensures *sum == array_int_sum(a, N-1);
*/


void sum_max(int* a, int N, int* max, int* sum){

  int i = 1;

  *sum = a[0];
  *max = a[0];
  
  /*@ loop invariant \forall integer k; 0 <= k < i ==> a[k] <= *max;
    @ loop invariant \exists integer k; 0 <= k < i && a[k] == *max;
    @ loop invariant *sum == array_int_sum(a, i-1);
    @ loop invariant 0 <= i <= N;
    @ loop invariant \separated(max, sum, a+(0..(N-1)));
    @ loop assigns *max, i, *sum;
    @ loop variant (N - i);
  */
  for (; i<N; i++){
    
    if (*max < a[i]){
      
      *max = a[i];
      
    }    
    *sum += a[i];
    
  }


}
