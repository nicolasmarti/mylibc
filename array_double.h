#ifndef ARRAY_DOUBLE_H
#define ARRAY_DOUBLE_H

/*@ inductive permut_double{L1, L2}(double *a1, double *a2, integer l, integer h){
  @ case permut_double_refl{L1, L2}:
  @      \forall double *a1, *a2, integer l, h;
  @              (\forall integer k; l <= k <= h ==> \at(a1[k], L1) == \at(a2[k], L2)) ==> permut_double{L1, L2}(a1, a2, l, h);
  @ case permut_double_swap{L1, L2}:
  @      \forall double *a1, *a2, integer l, h, i, j;
  @              (\forall integer k; l <= k <= h ==> k != i ==> k != j ==> \at(a1[k], L1) == \at(a2[k], L2)) ==> 
  @              (\at(a1[i], L1) == \at(a2[j], L2) && \at(a1[j], L1) == \at(a2[i], L2)) ==>
  @              permut_double{L1, L2}(a1, a2, l, h);
  @ case permut_double_trans{L1, L2, L3}:
  @      \forall double *a1, *a2, *a3, integer l, h;
  @      permut_double{L1, L2}(a1, a2, l, h) ==> permut_double{L2, L3}(a2, a3, l, h) ==> permut_double{L1, L3}(a1, a3, l, h);
  @ case permut_double_compo{L1, L2}:
  @      \forall double *a1, *a2, integer l, i, j, h;
  @        j == i + 1 ==>
  @        permut_double{L1, L2}(a1, a2, l, i) ==> permut_double{L1, L2}(a1, a2, j, h) ==> permut_double{L1, L2}(a1, a2, l, h);
  @ 
  @ }
  @
*/

/*@
  @ predicate gte_array_double{L}(double * a, integer l, integer h, double m) =
  @    \forall integer k; l <= k <= h ==> \at( a[k], L) <= m;
  @
  @ predicate gt_array_double{L}(double * a, integer l, integer h, double m) =
  @    \forall integer k; l <= k <= h ==> \at( a[k], L) < m;
  @
  @ predicate lte_array_double{L}(double * a, integer l, integer h, double m) =
  @    \forall integer k; l <= k <= h ==> \at( a[k], L) >= m;
  @
  @ predicate lt_array_double{L}(double * a, integer l, integer h, double m) =
  @    \forall integer k; l <= k <= h ==> \at( a[k], L) > m;
  @
*/

/*@
  @ axiomatic permut_extra {
  @
  @ axiom lt_permut_conserve{L1, L2}:
  @    \forall double *a1, *a2, double m, integer l, h;
  @       lt_array_double{L1}(a1, l, h, m) ==>
  @       \at( m, L1 ) == \at( m, L2) ==>
  @          lt_array_double{L2}(a2, l, h, m);
  @
  @ axiom lte_permut_conserve{L1, L2}:
  @    \forall double *a1, *a2, double m, integer l, h;
  @       lte_array_double{L1}(a1, l, h, m) ==>
  @       \at( m, L1 ) == \at( m, L2) ==>
  @          lte_array_double{L2}(a2, l, h, m);
  @
  @ axiom gt_permut_conserve{L1, L2}:
  @    \forall double *a1, *a2, double m, integer l, h;
  @       gt_array_double{L1}(a1, l, h, m) ==>
  @       \at( m, L1 ) == \at( m, L2) ==>
  @          gt_array_double{L2}(a2, l, h, m);
  @
  @ axiom gte_permut_conserve{L1, L2}:
  @    \forall double *a1, *a2, double m, integer l, h;
  @       gte_array_double{L1}(a1, l, h, m) ==>
  @       \at( m, L1 ) == \at( m, L2) ==>
  @          gte_array_double{L2}(a2, l, h, m);
  @ }
*/

/*@ predicate ordered_array_double{L}( double *a, integer l, integer h) =
  @    \forall integer k; l <= k < h ==> \at( a[k], L) <= \at( a[k+1], L);
*/

/*@
  @ axiomatic ordered_array_double_extra{
  @
  @ axiom ordered_array_double_extra{L}:
  @    \forall double *a, double v, integer l1, l2, m, h1, h2;
  @            ordered_array_double{L}(a, l1, h1) ==>
  @            ordered_array_double{L}(a, l2, h2) ==>
  @            gt_array_double(a, l1, h1, v)  ==>
  @            lte_array_double(a, l2, h2, v)  ==>
  @            v == \at( a[m], L) ==>
  @            m == h1 + 1 ==>
  @            l2 == m + 1 ==>
  @            ordered_array_double{L}(a, l1, h2);
  @}
*/


/*@ predicate contains{L}(double *array, integer l, integer h, double v) =
  @ \exists integer k; l <= k <= h && array[k] == v;
*/

/*@
  @ axiomatic contains_extra{
  @
  @ axiom not_contains_compo{L}:
  @   \forall double *array, integer l1, h1, l2, h2, double v;
  @       !contains(array, l1, h1, v) ==>
  @       !contains(array, l2, h2, v) ==>
  @       l2 <= h1 ==>
  @       !contains(array, l1, h2, v);
  @
  @ axiom not_contains_right{L}:
  @   \forall double *array, integer l, h, double v;
  @       ordered_array_double(array, l, h) ==>
  @       array[h] < v ==>
  @       !contains(array, l, h, v);
  @
  @ axiom not_contains_left{L}:
  @   \forall double *array, integer l, h, double v;
  @       ordered_array_double(array, l, h) ==>
  @       v < array[l] ==>
  @       !contains(array, l, h, v);
  @
  @ }

*/


#endif
