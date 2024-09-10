procedure find_min_up_to(a: [int]int, alength: int)
  returns (b: [int]int)
  requires 0 <= alength;
  ensures forall j: int, k: int ::
    0 <= alength && 0 <= j && 0 <= k && j <= k && k < alength ==>
      b[k] <= a[j];
  ensures 0 <= alength ==>
    (forall j: int :: exists k: int :: 0 <= j && j < alength ==>
      0 <= k && k < j && b[j] == a[k]);
  ensures forall j: int, k: int ::
    0 <= alength && 0 <= j && 0 <= k && k <= j && j < alength ==>
      b[j] <= b[k];
{
	var i: int := 0;
	var m: int := 0;
	while (i < alength)
	{
		if (a[i] < a[m])
		{
			b := b[i := a[i]];
			m := i;
		}
		else
		{
			b := b[i := a[m]];
		}
		i := i + 1;
	}
}
