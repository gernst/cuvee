procedure find_max_local(a: [int]int, alength: int)
  returns (b: [int]int, blength: int)
  requires 1 <= alength;
  ensures forall k: int ::
    (1 <= alength && 0 <= k && k < alength &&
      (forall l: int :: 0 <= l && l < k ==> a[l] < a[k])) ==>
        exists j: int :: 0 <= j && j < blength && a[k] == b[j];
  ensures forall j: int :: exists k: int ::
    1 <= alength && 0 <= j && j < blength ==>
      0 <= k && k < alength && b[j] == a[k];
  ensures forall j: int, k: int ::
    1 <= alength && 0 <= j && 0 <= k && j <= k && k < blength ==>
      b[j] <= b[k];
{
	b := b[0 := a[0]];
	blength := 1;

	var i: int := 1;
	var m: int := 0;
	while (i < alength)
	{
		if (a[i] > a[m])
		{
			b := b[i := a[i]];
			blength := blength + 1;
			m := i;
		}
		else
		{
		}
		i := i + 1;
	}
}
