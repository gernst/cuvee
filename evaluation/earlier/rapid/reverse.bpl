// similar to copy, but in reverse

procedure reverse(b: [int]int, length: int)
  returns (a: [int]int)
  requires 0 <= length;
  ensures forall j: int :: 0 <= length && 0 <= j && j < length ==>
    a[j] == b[(length - 1) - j];
{
	var i: int := 0;
	while(i < length)
	{
		a := a[i := b[length - 1 - i]];
		i := i + 1;
	}
}
