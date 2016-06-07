
//@ logic integer array_int_sum{L}(int *array, integer n) = (n < 0) ? 0 : (array[n] + array_int_sum(array, n-1));


/*@ requires \valid(a+(0..(N-1)));
  @ requires N > 0;
  @ requires \valid(max);
  @ requires \valid(sum);
  @ requires \separated(max, sum, a+(0..(N-1)));
  @
  @ assigns *sum, *max;
  @
  @ ensures \forall integer k; 0 <= k < N ==> a[k] <= *max;
*/


void sum_max2(int* a, int N, int* max, int* sum){

  *sum = 0;
  *max = 0;
  int i = 0;
  
  /*@ loop invariant \forall integer k; 0 <= k < i ==> a[k] <= *max;
    @ loop invariant *sum == array_int_sum(a, i-1);
    @ loop invariant 0 <= i <= N;
    @ loop invariant \separated(max, sum, a+(0..(N-1)));
    @ loop assigns *max, i, *sum;
    @ loop variant (N - i);
  */
  for (; i<N; i++){

    //@ assert i < N;

    //@ assert *sum == array_int_sum(a, i-1);
    
    if (*max < a[i]){
      
      *max = a[i];

      //@ assert *sum == array_int_sum(a, i-1);
      
      
    } else {


      //@ assert *sum == array_int_sum(a, i-1);


    }

    //@ assert *sum == array_int_sum(a, i-1);
    
    *sum += a[i];

    //@ assert *sum == array_int_sum(a, i-1) + a[i];
    
  }


}
