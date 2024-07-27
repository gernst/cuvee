extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int main()
{
  int i;
  int N;
  int a[N];
  int b[N];

  for(i=1;i<N;i++) {
    int j,k;
    __VERIFIER_assume(-10000 < j && j < 10000);
    __VERIFIER_assume(-10000 < k && k < 10000);
    __VERIFIER_assume(j <= k);
    a[i]=k;
    b[i]=j;
  }

  for(i=0;i<N;i++){
    a[i]=a[i]+1;
    b[i]=b[i]+1;
  }

  for(i=1;i<N;i++)
    __VERIFIER_assert(a[i] >= b[i]);
}

