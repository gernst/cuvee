procedure swap(length: int)
  returns (a: [int]int, b: [int]int)
  requires 0 <= length;
  ensures forall pos: int :: 0 <= length && 0 <= pos && pos < length ==>
    a[pos] == old(b)[pos];
  ensures forall pos: int :: 0 <= length && 0 <= pos && pos < length ==>
    b[pos] == old(a)[pos];
{
	var i: int := 0;
	while(i < length)
    decreases length - i;
    invariant 0 <= i;
	{
		var current: int := a[i];
		a := a[i := b[i]];
		b := b[i := current];
		i := i + 1;
	}
}

//(conjecture
//	(forall ((pos Int))
//		(=>
//			(and
//				(<= 0 length)
//				(<= 0 pos)
//				(< pos length)
//			)
//			(= (a main_end pos) (b l8 pos))
//		)
//	)
//)
//
//(conjecture
//	(forall ((pos Int))
//		(=>
//			(and
//				(<= 0 length)
//				(<= 0 pos)
//				(< pos length)
//			)
//			(= (b main_end pos) (a l8 pos))
//		)
//	)
//)
