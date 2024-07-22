extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int main()
{
  int i;
  int j;
  int N;
  int a[N];
  int b[N];

  for(i=1;i<N;i++) {
    int k;
    __VERIFIER_assume(j <= k);
    a[i] = k;
  }

  for(i=0;i<N;i++) {
    b[i] = a[i];
  }

  for(i=1;i<N;i++)
    __VERIFIER_assert(b[i] >= j);
}
