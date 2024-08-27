procedure copy_absolute(blength: int, b: [int]int)
  returns (a: [int]int)
  requires 0 <= blength;
  ensures forall k: int :: 0 <= k && k < blength ==>
    a[k] == b[k] || a[k] == 0 - b[k];
  ensures forall k: int :: 0 <= k && k < blength ==>
    0 <= a[k];
{
	var i: int := 0;
	while(i < blength)
    decreases blength - i;
    invariant 0 <= i;
	{
		if(b[i] >= 0)
		{
			a := a[i := b[i]];
		}
		else
		{
			a := a[i := 0 - b[i]];
		}
		i := i + 1;
	}
}

//(conjecture
//	(forall ((k Int))
//		(=>
//			(and
//				(<= 0 k)
//				(< k blength)
//			)
//			(or
//				(= (a main_end k) (b k) )
//				(= (a main_end k) (- 0 (b k)) )
//			)
//		)
//	)
//)
//
//(conjecture
//	(forall ((k Int))
//		(=>
//			(and
//				(<= 0 k)
//				(< k blength)
//			)
//				(<= 0 (a main_end k))
//		)
//	)
//)
