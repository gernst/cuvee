extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int main()
{
  int i;
  int j;
  int N;
  int a[N+1];
  int b[N];

  __VERIFIER_assume(j < 10000 && j > -10000);
  
  for(i=0;i<N;i++) {
    /* __VERIFIER_assume(a[i] < 10000 && a[i] > -10000); */
    /* if (j > a[i]) */
    /*   j = a[i]; */
    int k;
     __VERIFIER_assume(k < 10000 && k > -10000);
    __VERIFIER_assume(k >= j);
    a[i] = k;
  }

  for(i=0;i<N;i++) {
    b[i] = a[i]-j;
  }

  for(i=0;i<N;i++)
    __VERIFIER_assert(b[i] >= 0);
}
