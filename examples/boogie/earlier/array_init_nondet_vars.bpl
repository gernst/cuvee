procedure array_init_nondet_vars(n: int)
  returns (a: [int]int)
  requires 0 < n;
{
  // will currently not work cause: assume in while
  var i: int := 1;

  var j: int;
  assume 0 < j && j < 10000;

  var M: [int]bool;
  assume forall x: int :: M[x] == false;

  var k0: int;

  while(i < n)
    decreases n - i;
    invariant 1 <= i && i <= n;
    invariant forall x: int :: M[x] <==> exists i_: int :: x == i_  && 1 <= i_ && i_ < i;
    invariant forall x: int :: M[x]  ==> exists i_: int :: x == i_  && exists k_: int :: 0 < k_ && k_ < 10000 && a[x] == (i_ + j + k_);
  {
    var k: int;
    assume 0 < k && k < 10000;

    a := a[i := (i + j + k)];
    M := M[i := true];
    i := i + 1;
  }
  assert forall x: int :: 1 <= x && x < n ==> a[x] >= (x + 2);
}
//int main()
//{
//  int i;
//  int j=__VERIFIER_nondet_int();
//  int n=__VERIFIER_nondet_int();
//  assume_abort_if_not(n < 100000);
//  int a[n];
//
//  assume_abort_if_not(j>0 && j < 10000);
// 
//  for(i=1;i<n;i++) {
//    int k=__VERIFIER_nondet_int();
//    assume_abort_if_not(k>0 && k < 10000);
//    a[i]=i+j+k;
//  }
//
//  for(i=1;i<n;i++)
//    __VERIFIER_assert(a[i]>=(i+2));
//  return 0;
//}  
