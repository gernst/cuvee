procedure find_max_local(a: [int]int, alength: int)
  returns (b: [int]int, blength: int)
  requires 1 <= alength;
  ensures forall k: int :: 1 <= alength && 0 <= k && k < alength &&
    (forall l: int :: 0 <= l && l < k ==> a[l] < a[k]) ==>
      exists j: int :: 0 <= j && j < blength && a[k] == b[j];
  ensures forall j: int :: exists k: int ::
    1 <= alength && 0 <= j && j < blength ==>
      0 <= k && k < alength && b[j] == a[k];
  ensures forall j: int, k: int ::
    1 <= alength && 0 <= j && 0 <= k && j <= k && k < blength ==>
      b[j] <= b[k];
{
	b := b[0 := a[0]];
	blength := 1;

	var i: int := 1;
	var m: int := 0;
	while (i < alength)
	{
		if (a[i] > a[m])
		{
			b := b[i := a[i]];
			blength := blength + 1;
			m := i;
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
//				(<= 1 alength)
//				(<= 0 k)
//				(< k alength)
//				(forall ((l Int))
//					(=>
//						(and
//							(<= 0 l)
//							(< l k)
//						)
//						(< (a l) (a k))
//					)
//				)
//			)
//			(exists ((j Int))
//				(and
//					(<= 0 j)
//					(< j (blength main_end))
//					(= (a k) (b main_end j))
//				)
//			)
//		)
//	)
//)
//
//(conjecture
//	(forall ((j Int))
//		(exists ((k Int))
//			(=>
//				(and
//					(<= 1 alength)
//					(<= 0 j)
//					(< j (blength main_end))
//				)
//				(and
//					(<= 0 k)
//					(< k alength)
//					(= (b main_end j) (a k))
//				)
//			)
//		)
//	)
//)
//
//(conjecture
//	(forall ((j Int)(k Int))
//		(=>
//			(and
//				(<= 1 alength)
//				(<= 0 j)
//				(<= 0 k)
//				(<= j k)
//				(< k (blength main_end))
//			)
//			(<= (b main_end j) (b main_end k))
//		)
//	)
//)
