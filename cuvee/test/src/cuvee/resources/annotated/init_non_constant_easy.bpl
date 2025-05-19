// Variation of init_non_constant, where multiplication is removed.
// Properties:
// 1) after the execution, a[pos] has the value pos+v for each position pos in the array
// 2) if v is greater than 0, a[pos] is greater than pos
// 3) if v is strictly greater than 0, a[pos] is strictly greater than pos (variation of property 2)
// 4) if v is some positive constant, a[pos] is strictly greater than pos (variation of property 2)

procedure init_non_constant_easy(alength: int, v: int)
  returns (a: [int]int)
  requires 0 <= alength;
  ensures forall pos: int ::
    0 <= alength && 0 <= pos && pos < alength ==>
      a[pos] == pos + v;
  ensures forall pos: int ::
    0 <= alength && 0 <= pos && pos < alength && 0 <= v ==>
      pos <= a[pos];
  ensures forall pos: int ::
    0 <= alength && 0 <= pos && pos < alength && 0 < v ==>
      pos < a[pos];
  ensures forall pos: int ::
    0 <= alength && 0 <= pos && pos < alength && v == 80 ==>
      pos < a[pos];
{
	var i: int := 0;
	while(i < alength)
    decreases alength - i;
    invariant forall pos: int ::
      0 <= pos && pos < i ==> a[pos] == pos + v;
    invariant forall pos: int ::
      0 <= pos && pos < i && 0 <= v ==> pos <= a[pos];
    invariant forall pos: int ::
      0 <= pos && pos < i && 0 < v ==> pos < a[pos];
    invariant forall pos: int ::
      0 <= pos && pos < i && v == 80 ==> pos < a[pos];
	{
		a := a[i := i + v];
		i := i + 1;
	}
}

//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 alength)
//            (<= 0 pos)
//            (< pos alength)
//         )
//         (= (a main_end pos) (+ pos v))
//      )
//   )
//)
//
//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 alength)
//            (<= 0 pos)
//            (< pos alength)
//            (<= 0 v)
//         )
//         (<= pos (a main_end pos))
//      )
//   )
//)
//
//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 alength)
//            (<= 0 pos)
//            (< pos alength)
//            (< 0 v)
//         )
//         (< pos (a main_end pos))
//      )
//   )
//)
//
//(conjecture
//   (forall ((pos Int))
//      (=>
//         (and
//            (<= 0 alength)
//            (<= 0 pos)
//            (< pos alength)
//            (= v 80)
//         )
//         (< pos (a main_end pos))
//      )
//   )
//)
