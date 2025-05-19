// initialize each position in the array to the value of the previous position + 1, starting with value v for the first element
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_seq_init_true-unreach-call_ground.c

procedure init_previous_plus_one_alternative(alength: int, v: int)
  returns (a: [int]int)
  requires 0 <= alength;
  ensures forall pos: int :: 0 <= pos && (pos + 1) < alength && 0 <= alength ==>
    a[pos] <= a[pos + 1];
  ensures forall pos: int :: 0 <= pos && (pos + 1) < alength && 0 <= alength ==>
    a[pos] < a[pos + 1];
{
  a := a[0 := v];
  var i: int := 1;
	while(i < alength)
    decreases alength - i;
    invariant forall pos: int :: 0 <= pos && (pos + 1) < i ==>
      a[pos] <= a[pos + 1];
    invariant forall pos: int :: 0 <= pos && (pos + 1) < i ==>
      a[pos] < a[pos + 1];
	{
		a := a[i := a[i-1] + 1];
		i := i + 1;
	}
}

//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 pos)
//            (< (+ pos 1) alength)
//            (<= 0 alength)
//         )
//         (<= (a main_end pos) (a main_end (+ pos 1)))
//      )
//   )
//)
//
//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 pos)
//            (< (+ pos 1) alength)
//            (<= 0 alength)
//         )
//         (< (a main_end pos) (a main_end (+ pos 1)))
//      )
//   )
//)
