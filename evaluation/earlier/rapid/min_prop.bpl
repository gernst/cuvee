procedure min_prop(b: [int]int, blength: int)
  returns (a: [int]int)
  requires 0 <= blength;
  ensures forall pos: int :: 0 <= pos && pos < blength && 0 <= blength ==>
    a[pos] <= 0;
  ensures forall pos: int :: 0 <= pos && pos < blength && 0 <= blength ==>
    a[pos] == 0 || a[pos] == b[pos];
{
	var i: int := 0;
	while(i < blength)
	{
    if(b[i] < 0)
    {
       a := a[i := b[i]];
    }
    else
    {
       a := a[i := 0];
    }
		i := i + 1;
	}
}
