procedure in_place_max(alength: int)
  returns (a: [int]int)
  requires 0 <= alength;
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < alength ==>
    0 <= a[pos];
{
	var i: int := 0;
	while (i < alength)
    decreases alength - i;
    invariant 0 <= i;
	{
		if(a[i] < 0)
		{
			a := a[i := 0];
		}
		else
		{
		}
		i := i + 1;
	}
}

//(conjecture
//	(forall ((pos Int))
//		(=>
//			(and
//				(<= 0 alength)
//				(<= 0 pos)
//				(< pos alength)
//			)
//			(<= 0 (a main_end pos))
//		)
//	)
//)
