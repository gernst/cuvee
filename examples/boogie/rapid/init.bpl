procedure init(alength: int, v: int)
  returns (a: [int]int)
  requires 0 <= alength;
  ensures forall pos: int :: 0 <= pos && pos < alength && 0 <= alength ==>
    a[pos] == v;
{
	var i: int := 0;
	while(i < alength)
    decreases alength - i;
    invariant 0 <= i;
	{
		a := a[i := v];
		i := i + 1;
	}
}

//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 pos)
//            (< pos alength)
//            (<= 0 alength)
//         )
//         (= (a main_end pos) v)
//      )
//   )
//)
