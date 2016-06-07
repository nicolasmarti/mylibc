
/*@ requires \valid(a+(0..(N-1)));
  @ assigns *sum, *max;
*/


void sum_max(int* a, int N, int *sum, int *max){

  *sum = 0;
  *max = 0;
  int i = 0;

  /*@ loop invariant \forall integer k; 0 <= k < i ==> a[k] <= *max;
    @ loop invariant N > 0 ==> \exists integer k; a[k] == max;
    @ loop assigns i, *sum, *max;
    @ loop variant (N - i);
  */
  
  for (; i<N; i++){
    if (*max < a[i]){
      *max = a[i];
    }
    *sum += a[i];
  }


}
