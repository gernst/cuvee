// increment each position in the array by one, then check that every position was incremented by 1
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_43_true-unreach-call_ground.c,
// 1) original property
// 2) slightly-rewritten property

procedure increment_by_one(a: [int]int, alength: int)
  returns (b: [int]int)
  requires 0 <= alength;
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < alength ==>
    a[pos] == (b[pos] - 1);
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < alength ==>
    b[pos] == (a[pos] + 1);
{
	var i: int := 0;

	while (i < alength)
	{
		b := b[i := a[i] + 1];
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
//			(= (a pos) (- (b main_end pos) 1))
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
//			(= (b main_end pos) (+ (a pos) 1))
//		)
//	)
//)
