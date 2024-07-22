extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
int main()
{
  int i;
  int N;
  int a[N];
  int b[N];
  int c[N];

   __VERIFIER_assume(N < 1000);
  
  for(i=1;i<N;i++) {
    int x;
    /* __VERIFIER_assume(x>0 && x < 1000); */
    __VERIFIER_assume(x <= y);
    a[i]=x;
    b[i]=y;
  }

  for(i=0;i<N;i++){
    c[i]=b[i]-a[i];
  }

  for(i=1;i<N;i++)
    __VERIFIER_assert(c[i] >= 0);
}

