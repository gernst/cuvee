extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int main()
{
  int i;
  int N;
  int a[N];

  for(i=1;i<N;i++) {
    int	j;
    __VERIFIER_assume(0 <= j && j < 10000);
    a[i]=j;
  }

  for(i=0;i<N;i++){
    a[i]=a[i]+1;
    a[i]=a[i]+1;
  }

  for(i=1;i<N;i++)
    __VERIFIER_assert(a[i] >= 2);
}


