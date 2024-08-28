function P(x: int): bool { 0 != x }

procedure copy_positive(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength;
  ensures forall k: int :: 0 <= k && k < alength ==>
    0 != a[k];
{
	var i: int := 0;
	alength := 0;
	while(i < blength)
    decreases blength - i;
    invariant 0 <= i;
	{
		if (0 != b[i]) {
			a[alength] := b[i];
			alength := alength + 1;
		}
		i := i + 1;
	}
}
