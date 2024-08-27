// for each position p: if a[p] is 1, set b[p] to 1, otherwise set it to zero.
// Prove that either both a[p] is 1 and b[p] is 1, or both a[p] is not 1 and b[p] is zero
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_running_true-unreach-call.c
// but simplified

procedure both_or_none(a: [int]int, alength: int)
  returns (b: [int]int)
  requires 0 <= alength;
  ensures forall j: int :: 0 <= j && j < alength && 0 <= alength ==> 
    (a[j] == 1 && b[j] == 1) || (a[j] != 1 && b[j] == 0);
{
  var i: int := 0;

  while(i < alength)
    decreases alength - i;
    invariant 0 <= i;
  {
    if (a[i] == 1)
    {
      b := b[i := 1];
    }
    else
    {
      b := b[i := 0];
    }
    i := i + 1;
  }
}

//(conjecture
//  (forall ((j Int))
//    (=>
//      (and
//        (<= 0 j)
//        (< j alength)
//        (<= 0 alength)
//      )
//      (or
//        (and
//          (= (a j) 1)
//          (= (b main_end j) 1)
//        )
//        (and
//          (not (= (a j) 1) )
//          (= (b main_end j) 0)
//        )
//      )
//    )
//  )
//)
