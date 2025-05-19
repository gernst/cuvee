procedure copy_nonzero(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength;
  ensures forall k: int :: 0 <= blength && 0 <= k && k < alength ==>
    a[k] != 0;
  ensures forall k: int :: 
    exists l : int :: 0 <= k && 0 <= blength && k < alength ==>
      a[k] == b[l];
{
	var i: int := 0;
	alength := 0;
	while(i < blength)
    decreases blength - i;
    invariant 0 <= alength && alength <= i;
    invariant forall k: int :: 0 <= k && k < alength ==> a[k] != 0;
    invariant forall k: int :: 
      exists l : int :: 0 <= k && 0 <= i && k < alength ==> a[k] == b[l];
	{
		if (b[i] != 0)
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
//				(<= 0 blength)
//				(<= 0 k)
//				(< k (alength main_end))
//			)
//			(not (= (a main_end k) 0))
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
//					(<= 0 blength)
//					(< k (alength main_end))
//				)
//				(= (a main_end k) (b l))
//			)
//		)
//	)
//)
