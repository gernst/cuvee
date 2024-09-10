procedure copy_two_indices(b: [int]int, blength: int)
  returns (a: [int]int)
  requires 0 <= blength;
  ensures forall k: int :: 0 <= blength && 0 <= k && k < blength ==>
    a[k] == b[k];
{
	var i: int := 0;
	var j: int := 0;
	while(i < blength)
	{
		a := a[i := b[j]];
		i := i + 1;
		j := j + 1;
	}
}
