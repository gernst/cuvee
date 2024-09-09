// generate a new array b containing all indices where the arrays a1 and a2 have the same value.
// Properties:
// 1) Each element of b corresponds to a position in a1/a2.
// 2) For each element of b, the elements in a1 and a2 at the corresponding index are the same.
// 3) If the elements in a1 and a2 are the same at position pos, then there exists an element in b with value pos.
// 4) If the elements in a1 and a2 are the same at position pos, then there exists an element in b with value pos, and that element is between 0 and blength.

procedure collect_indices_equal_values(a1: [int]int, a2: [int]int, alength: int)
  returns (b: [int]int, blength: int)
  requires 0 <= alength;
  ensures forall pos: int ::  0 <= alength && 0 <= pos && pos < blength ==>
    0 <= b[pos] && b[pos] < alength;
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < blength ==>
    a1[b[pos]] == a2[b[pos]];
  ensures forall pos: int ::
    0 <= alength && 0 <= pos && pos < alength && a1[pos] == a2[pos] ==>
      exists pos2: int :: b[pos2] == pos;
  ensures forall pos: int ::
    0 <= alength && 0 <= pos && pos < alength && a1[pos] == a2[pos] ==>
      exists pos2: int :: 0 <= pos2 && pos2 < blength && b[pos2] == pos;
{
  blength := 0;

	var i: int := 0;
	while(i < alength)
	{
    if(a1[i] == a2[i])
    {
      b := b[blength := i];
      blength := blength + 1;
    }
    else
    {
    }
    i := i + 1;
	}
}

//(conjecture
//   (forall ((pos Int))
//      (=>
//        (and
//          (<= 0 alength)
//          (<= 0 pos)
//          (< pos (blength main_end))
//        )
//        (and
//          (<= 0 (b main_end pos))
//          (< (b main_end pos) alength)
//        )
//      )
//   )
//)
//
//(conjecture
//  (forall ((pos Int))
//    (=>
//      (and
//        (<= 0 alength)
//        (<= 0 pos)
//        (< pos (blength main_end))
//      )
//      (= (a1 (b main_end pos)) (a2 (b main_end pos)))
//    )
//  )
//)
//
//(conjecture
//  (forall ((pos Int))
//    (=>
//      (and
//        (<= 0 alength)
//        (<= 0 pos)
//        (< pos alength)
//        (= (a1 pos) (a2 pos))
//      )
//      (exists ((pos2 Int))
//        (and
//          (= (b main_end pos2) pos)
//        )
//      )
//    )
//  )
//)
//
//(conjecture
//  (forall ((pos Int))
//    (=>
//      (and
//        (<= 0 alength)
//        (<= 0 pos)
//        (< pos alength)
//        (= (a1 pos) (a2 pos))
//      )
//      (exists ((pos2 Int))
//        (and
//          (<= 0 pos2)
//          (< pos2 (blength main_end))
//          (= (b main_end pos2) pos)
//        )
//      )
//    )
//  )
//)
