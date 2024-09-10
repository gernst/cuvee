procedure copy_partial(blength: int, k: int, b: [int]int)
  returns (a: [int]int)
  requires 0 <= k;
  ensures k <= blength ==> 
    forall j: int :: 0 <= j && j < k ==> a[j] == b[j];
{
	var alength: int := 0;

	while(alength < k)
	{
		a := a[alength := b[alength]];
		alength := alength + 1;
	}
}

//(conjecture
//	(=>
//		(<= k blength)
//		(forall ((j Int))
//			(=>
//				(and
//					(<= 0 j)
//					(< j k)
//				)
//				(= (a main_end j) (b j))
//			)
//		)
//	)
//)
