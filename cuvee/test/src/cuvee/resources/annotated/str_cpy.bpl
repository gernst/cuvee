procedure str_cpy(b: [int]int, length: int)
  returns (a: [int]int, i: int)
  requires 0 <= length;
  ensures forall pos: int :: 0 <= length && 0 <= pos && pos < i ==>
    a[pos] == b[pos];
  ensures forall pos: int :: 0 <= length && 0 <= pos && pos < i ==>
    a[pos] != 0;
  ensures forall pos: int :: 0 <= length && 0 <= pos && pos < i ==>
    b[pos] != 0;
  ensures 0 <= length && i < length ==> b[i] == 0;
{
	i := 0;
	while(i < length && b[i] != 0)
    decreases length - i;
    invariant forall pos: int :: 0 <= pos && pos < i ==> a[pos] == b[pos];
    invariant forall pos: int :: 0 <= pos && pos < i ==> a[pos] != 0;
    invariant forall pos: int :: 0 <= pos && pos < i ==> b[pos] != 0;
	{
		a := a[i := b[i]];
		i := i + 1;
	}
}

//(conjecture
//	(forall ((pos Int))
//		(=>
//			(and
//				(<= 0 length)
//				(<= 0 pos)
//				(< pos (i main_end))
//			)
//			(= (a main_end pos) (b pos) )
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
//				(< pos (i main_end))
//			)
//			(not (= (a main_end pos) 0))
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
//				(< pos (i main_end))
//			)
//			(not (= (b pos) 0))
//		)
//	)
//)
//
//(conjecture
//	(=>
//		(and
//			(<= 0 length)
//			(< (i main_end) length)
//		)
//		(= (b (i main_end)) 0)
//	)
//)
