//@ predicate sorted(integer a[], integer n) = \forall integer i; 0 <= i < n ==> a[i] <= a[i + 1];

/*@
   requires \valid(a + (0..n-1));
   requires sorted(a, n);
 */
int search(int a[], int n) {
    return 0;
}