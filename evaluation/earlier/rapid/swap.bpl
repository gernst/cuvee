procedure swap(length: int)
  returns (a: [int]int, b: [int]int)
  requires 0 <= length;
  ensures forall pos: int :: 0 <= length && 0 <= pos && pos < length ==>
    a[pos] == old(b)[pos];
  ensures forall pos: int :: 0 <= length && 0 <= pos && pos < length ==>
    b[pos] == old(a)[pos];
{
	var i: int := 0;
	while(i < length)
	{
		var current: int := a[i];
		a := a[i := b[i]];
		b := b[i := current];
		i := i + 1;
	}
}
