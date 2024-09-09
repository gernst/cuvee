procedure init_partial(alength: int, k: int)
  returns (a: [int]int)
  requires 0 <= alength && 0 <= k;
  ensures forall pos: int ::
    0 <= pos && pos < k && k <= alength && 0 <= alength ==>
      a[pos] == 0;
{
	var i: int := 0;
	while (i < k)
	{
		a := a[i := 0];
		i := i + 1;
	}
}

//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 pos)
//            (< pos k)
//            (<= k alength)
//            (<= 0 alength)
//         )
//         (= (a main_end pos) 0)
//      )
//   )
//)
