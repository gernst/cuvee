procedure copy(blength: int, b: [int]int)
returns (a: [int]int)
  requires 0 <= blength;
  ensures forall j: int :: 0 <= blength && 0 <= j && j < blength ==>
    a[j] == b[j];
{
	var i: int := 0;

	while(i < blength)
	{
		a := a[i := b[i]];
		i := i + 1;
	}
}

//(conjecture
//	(forall ((j Int))
//		(=>
//			(and
//				(<= 0 blength)
//				(<= 0 j)
//				(< j blength)
//			)
//			(= (a main_end j) (b j))
//		)
//	)
//)
