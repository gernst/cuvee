// harder version of increment_by_one (it is harder, since the array we read from is the same array we write to)
// increment each position in the array by one, then check that every position was incremented by 1
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_43_true-unreach-call_ground.c,
// 1) original property
// 2) slightly-rewritten property

procedure increment_by_one_harder(alength: int)
  returns (a: [int]int)
  requires 0 <= alength;
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < alength ==>
    old(a)[pos] == (a[pos] - 1);
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < alength ==>
    a[pos] == (old(a)[pos] + 1);
{
	var i: int := 0;

	while (i < alength)
	{
		a := a[i := a[i] + 1];
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
//			(= (a l12 pos) (- (a main_end pos) 1))
//		)
//	)
//)
//
//(conjecture
//	(forall ((pos Int))
//		(=>
//			(and
//				(<= 0 alength)
//				(<= 0 pos)
//				(< pos alength)
//			)
//			(= (a main_end pos) (+ (a l12 pos) 1))
//		)
//	)
//)
