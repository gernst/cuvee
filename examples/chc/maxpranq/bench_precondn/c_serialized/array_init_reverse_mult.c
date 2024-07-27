extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int main()
{
  int i;
  int N;
  int a[N];

  for(i=1;i<N;i++) {
    a[i]=1;
  }

  for(i=N-1;i>=0;i--){
    a[i]=a[i]-1;
  }

  for(i=1;i<N;i++)
    __VERIFIER_assert(a[i] == 0);
}

