// procedure copy_absolute(blength: int, b: [int]int)
//   returns (a: [int]int)
//   requires 0 <= blength;
//   ensures forall k: int :: 0 <= k && k < blength ==>
//     a[k] == b[k] || a[k] == 0 - b[k];
//   ensures forall k: int :: 0 <= k && k < blength ==>
//     0 <= a[k];
// {
// 	var i: int := 0;
// 	while(i < blength)
//     decreases blength - i;
//     invariant 0 <= i;
//     invariant forall x: int :: 0 <= x && x < i ==> 0 <= a[x];
//     invariant forall x: int :: 0 <= x && x < i ==> 
//         a[x] == b[x] || a[x] == 0 - b[x];
// 	{
// 		if(b[i] >= 0)
// 		{
// 			a := a[i := b[i]];
// 		}
// 		else
// 		{
// 			a := a[i := 0 - b[i]];
// 		}
// 		i := i + 1;
// 	}
// }

// procedure copy_absolute_annotate(blength: int, b: [int]int)
//   returns (a: [int]int)
//   requires 0 <= blength;
//   // ensures forall k: int :: 0 <= k && k < blength ==>
//   //   a[k] == b[k] || a[k] == 0 - b[k];
//   // ensures forall k: int :: 0 <= k && k < blength ==>
//   //   0 <= a[k];
// {
// 	var i: int := 0;
// 	while(i < blength)
//     decreases blength - i;
//     invariant 0 <= i;
//     invariant forall x: int :: 0 <= x && x < i ==> (
//       (
//       ((exists t: int ::
//           (0 <= t && t < i) && (b[t] >= 0) && x == t)
//         ||
//        (exists f: int ::
//           (0 <= f && f < i) && !(b[f] >= 0) && x == f)
//       ) ==>
//       ((exists tt: int ::
//           (0 <= tt && tt < i) && (b[tt] >= 0) && x == tt && a[x] == b[tt])
//         ||
//        (exists ff: int ::
//           (0 <= ff && ff < i) && !(b[ff] >= 0) && x == ff && a[x] == 0 - b[ff])
//       )
//       ) && // TODO failing part
//       !((exists t: int ::
//           (0 <= t && t < i) && (b[t] >= 0) && x == t)
//         ||
//         (exists f: int ::
//           (0 <= f && f < i) && !(b[f] >= 0) && x == f)
//       ) ==> a[x] == old(a)[x]
//     );
// 	{
// 		if(b[i] >= 0)
// 		{
// 			a := a[i := b[i]];
// 		}
// 		else
// 		{
// 			a := a[i := 0 - b[i]];
// 		}
// 		i := i + 1;
// 	}
// }

procedure copy_absolute(blength: int, b: [int]int)
  returns (a: [int]int)
  requires 0 <= blength;
  ensures forall k: int :: 0 <= k && k < blength ==>
    a[k] == b[k] || a[k] == 0 - b[k];
  ensures forall k: int :: 0 <= k && k < blength ==>
    0 <= a[k];
{
	var i: int := 0;
	while(i < blength)
    decreases blength - i;
    invariant 0 <= i;
	{
		if(b[i] >= 0)
		{
			a := a[i := b[i]];
		}
		else
		{
			a := a[i := 0 - b[i]];
		}
		i := i + 1;
	}
}
