// similar to copy, but keeps track of the size of a and asserts the property with respect to the size of a

procedure push_back(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength;
  ensures forall j: int :: 0 <= blength && 0 <= j && j < alength ==>
    a[j] == b[j];
{
	alength := 0;
	var i: int := 0;
	while(i < blength) {
		a := a[i := b[i]];
		alength := alength + 1;
		i := i + 1;
	}
}
