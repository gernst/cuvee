procedure array_mul_init()
    returns (a: [int]int, b: [int]int)
{
  var n: int := 100000;
  var i: int := 0;
  var k: int;

  var M: [int]bool;
  assume forall x: int :: M[x] == false;

  while(i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    invariant forall x: int :: 
        M[x] <==> exists i_: int :: x == i_ && 0 <= i_ && i_ < i;
    invariant forall x: int :: 
        M[x]  ==> exists i_: int :: 
            x == i_ && a[x] == b[x];
  {
    a := a[i := i];
    b := b[i := i];
    M := M[i := true];
    i := i + 1;
  }

  var N: [int]bool;
  assume forall x: int :: N[x] == false;

  // I think this is not possible because of short
  i := 0;
  while(i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    invariant forall x: int :: 
        N[x] <==> exists i_: int :: x == i_ && 0 <= i_ && i_ < i;
    invariant forall x: int ::
        N[x]  ==> exists i_: int :: 
        x == i_ && (a[x] == b[x] || exists k_: int :: a[x] == k && b[x] == k * k);
  {
    var short: int;
		if(short != 0)
		{
      var tmp: int;
			k := tmp;
			a := a[i := k];
			b := b[i := k * k];
    N := N[i := true];
		}
    i := i + 1;
  }
  //assert forall x: int:: 
  //    0 <= x && x < n ==> (a[i] == b[i] || b[i] == a[i] * a[i]);
}
//#define SIZE 100000
//short __VERIFIER_nondet_short();
//int main()
//{
//	int a[SIZE];
//	int b[SIZE];
//	int k;
//	int i;
//
//	for (i  = 0; i<SIZE ; i++)
//	{
//		a[i] = i; 
//		b[i] = i ;
//	}
//
//	for (i=0; i< SIZE; i++)
//	{
//		if(__VERIFIER_nondet_short())
//		{
//			k = __VERIFIER_nondet_short();
//			a[i] = k;
//			b[i] = k * k ;
//		}
//	}
//
//	for (i=0; i< SIZE; i++)
//	{
//		__VERIFIER_assert(a[i] == b[i] || b[i]  == a[i] * a[i]);
//	}
//}
