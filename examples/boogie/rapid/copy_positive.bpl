procedure copy_positive(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength;
  ensures forall k: int :: 0 <= k && k < alength && 0 <= blength ==>
    0 <= a[k];
  ensures forall k: int :: exists l: int ::
    0 <= k && k < alength && 0 <= blength ==>
      a[k] == b[l];
{
	var i: int := 0;
	alength := 0;
	while(i < blength)
    decreases blength - i;
    invariant 0 <= i;
	{
		if (b[i] >= 0)
		{
			a := a[alength := b[i]];
			alength := alength + 1;
		}
		else
		{
		}
		i := i + 1;
	}
}

//(conjecture
//	(forall ((k Int))
//		(=>
//			(and
//				(<= 0 k)
//				(< k (alength main_end))
//				(<= 0 blength)
//			)
//			(<= 0 (a main_end k))
//		)
//	)
//)
//
//(conjecture
//	(forall ((k Int))
//		(exists ((l Int))
//			(=>
//				(and
//					(<= 0 k)
//					(< k (alength main_end))
//					(<= 0 blength)
//				)
//				(= (a main_end k) (b l))
//			)
//		)
//	)
//)
