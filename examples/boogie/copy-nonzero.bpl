procedure copy_nonzero(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength;
  ensures forall j: int ::
    0 <= j && j < alength ==> a[j] != 0;
{
	var i:  int := 0;
    
    alength := 0;

	while(i < blength)
        decreases blength - i;
        invariant 0 <= alength && alength <= i && i <= blength;
        // invariant forall j: int ::
        //     0 <= j && j < alength ==> exists k: int :: 0 <= k && k < i && b[k] != 0 && a[j] == b[k];
	{
        if(b[i] != 0) {
            a[alength] := b[i];
            alength := alength + 1;
        }

		i := i + 1;
	}
}