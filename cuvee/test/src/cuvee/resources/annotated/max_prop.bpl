procedure max_prop(b: [int]int, blength: int)
  returns (a: [int]int)
  requires 0 <= blength;
  ensures forall pos: int :: 0 <= pos && pos < blength && 0 <= blength ==>
    0 <= a[pos];
  ensures forall pos: int :: 0 <= pos && pos < blength && 0 <= blength ==>
    a[pos] == 0 || a[pos] == b[pos];
{
	var i: int := 0;
	while(i < blength)
    decreases blength - i;
    invariant forall pos: int :: 0 <= pos && pos < i ==> 0 <= a[pos];
    invariant forall pos: int :: 0 <= pos && pos < i ==>
      a[pos] == 0 || a[pos] == b[pos];
	{
    if(b[i] >= 0)
    {
       a := a[i := b[i]];
    }
    else
    {
       a := a[i := 0];
    }
		i := i + 1;
	}
}

//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 pos)
//            (< pos blength)
//            (<= 0 blength)
//         )
//         (<= 0 (a main_end pos))
//      )
//   )
//)
//
//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 pos)
//            (< pos blength)
//            (<= 0 blength)
//         )
//         (or
//            (= (a main_end pos) 0)
//            (= (a main_end pos) (b pos))
//         )
//      )
//   )
//)
