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
