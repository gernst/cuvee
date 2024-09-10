// for each position, subtract the element of array b from the element of array a and save the result in array c.
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_seq_init_true-unreach-call_ground.c,
// but subtraction replaced by addition

procedure vector_subtraction(a: [int]int, b: [int]int, length: int)
  returns (c: [int]int)
  requires 0 <= length;
  ensures forall j: int :: 0 <= j && j < length && 0 <= length ==>
    c[j] == (a[j] - b[j]);
{
	var i: int := 0;
	while(i < length)
	{
		c := c[i := a[i] - b[i]];
		i := i + 1;
	}
}
