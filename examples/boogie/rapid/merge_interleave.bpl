procedure merge_interleave(a: [int]int, b: [int]int, alength: int)
  returns (c: [int]int)
  requires 0 <= alength;
  ensures forall pos: int ::
    0 <= alength && 0 <= pos && pos < alength ==>
      c[pos * 2] == a[pos];
  ensures forall pos: int ::
    0 <= alength && 0 <= pos && pos < alength ==>
      c[(pos * 2) + 1] == b[pos];
  ensures forall pos: int :: exists j: int ::
    0 <= alength && 0 <= pos && pos < alength ==>
      c[pos] == a[j] || c[pos] == b[j];
{
	var i: int := 0;
	while(i < alength)
    decreases alength - i;
    invariant 0 <= i;
	{
    c := c[i * 2 := a[i]];
    c := c[i * 2 + 1 := b[i]];
		i := i + 1;
	}
}

//(conjecture
//   (forall ((pos Int))
//      (=>
//        (and
//          (<= 0 alength)
//          (<= 0 pos)
//          (< pos alength)
//        )
//        (= (c main_end (* pos 2)) (a pos))
//      )
//   )
//)
//
//(conjecture
//   (forall ((pos Int))
//      (=>
//        (and
//          (<= 0 alength)
//          (<= 0 pos)
//          (< pos alength)
//        )
//        (= (c main_end (+ (* pos 2) 1)) (b pos))
//      )
//   )
//)
//
//(conjecture
//   (forall ((pos Int))
//      (exists ((j Int))
//        (=>
//          (and
//            (<= 0 alength)
//            (<= 0 pos)
//            (< pos alength)
//          )
//          (or
//            (= (c main_end pos) (a j))
//            (= (c main_end pos) (b j))
//          )
//        )
//      )
//   )
//)
