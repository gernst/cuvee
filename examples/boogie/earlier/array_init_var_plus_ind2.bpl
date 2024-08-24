procedure array_init_var_plus_ind2(n: int)
  returns (a: [int]int)
  requires 0 <= n;
{
  // will currently not work cause: stop not initialized
  var i: int := 0;

  var j: int := 0;
  var k: int := 0;

  //var M: [int]bool;
  //assume forall x: int :: M[x] == false;

  while(i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    //invariant forall x: int :: M[x] <==> exists i_: int :: x == i_ && 0 <= i_ && i_ < i;
    //invariant forall x: int :: M[x]  ==> exists i_: int :: x == i_ && exists j_: int :: j == j_ && a[x] == j_;
  {
    var stop: int;
    if(stop != 0)
    {break;}
    else 
    {
    a := a[i := j];
    //M := M[i := true];
    j := j + i;
    k := k - i;
    i := i + 1;
    }
  }
  //assert forall x: int :: 0 <= x < i ==> a[x] >= k;
}
//int main()
//{
//  int i;
//  int j=0;
//  int k=0;
//  int a[N];
//
//  for(i=0;i<N;i++){
//    int x=__VERIFIER_nondet_int();
//    if(x) break;
//    a[i]=j;
//    j=j+i;
//    k=k-i;
//  }
//
//  for(int l=1;l<i;l++)
//    __VERIFIER_assert(a[l]>=k);
//  return 0;
//}

