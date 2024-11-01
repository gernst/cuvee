procedure init_conditionally(a: [int]int, b: [int]int, length: int)
  returns (c: [int]int, clength: int)
  requires 0 <= length;
  ensures forall pos: int :: 0 <= pos && pos < clength && 0 <= length ==>
    a[c[pos]] == b[c[pos]];
  ensures forall pos: int :: 0 <= pos && pos < clength && 0 <= length ==>
    pos <= c[pos];
{
	var i: int := 0;
	clength := 0;
	while(i < length)
	{
		if (a[i] == b[i])
		{
			c := c[clength := i];
			clength := clength + 1;
		}
		else
		{
		}
		i := i + 1;
	}
}
