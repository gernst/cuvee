// Properties
// 1) each element in b is greater or equal 0
// 2) each element in c is smaller than 0
// 3) each element in b is a copy of some element in a
// 4) each element in c is a copy of some element in a
// 5) for each element in a, which is greater or equal 0, there exists a copy of that element in b
// 6) for each element in a, which is smaller than 0, there exists a copy of that element in c
// 7) for each element in a, there exists a copy of that element either in b or in c.

procedure partition(a: [int]int, alength: int)
  returns (b: [int]int, c: [int]int, blength: int, clength: int)
  requires 0 <= alength;
  ensures forall pos: int :: 
    0 <= alength && 0 <= pos && pos < blength ==>
      0 <= b[pos];
  ensures forall pos: int :: 
    0 <= alength && 0 <= pos && pos < clength ==>
      c[pos] < 0;
  ensures forall pos: int :: 
    0 <= alength && 0 <= pos && pos < blength ==>
      (exists pos2: int :: b[pos] == a[pos2]);
  ensures forall pos: int :: 
    0 <= alength && 0 <= pos && pos < clength ==>
      (exists pos2: int :: c[pos] == a[pos2]);
  ensures forall pos: int :: 
    0 <= alength && 0 <= pos && pos < alength && 0 <= a[pos] ==>
      (exists pos2: int :: b[pos2] == a[pos]);
  ensures forall pos: int :: 
    0 <= alength && 0 <= pos && pos < alength && a[pos] < 0 ==>
      (exists pos2: int :: c[pos2] == a[pos]);
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < alength ==>
    ((exists pos2: int :: b[pos2] == a[pos]) ||
      (exists pos2: int :: c[pos2] == a[pos]));
{
  blength := 0;
  clength := 0;

	var i: int := 0;
	while(i < alength)
	{
      if(a[i] >= 0)
      {
        b := b[blength := a[i]];
        blength := blength + 1;
      }
      else
      {
        c := c[clength := a[i]];
        clength := clength + 1;
      }
      i := i + 1;
	}
}
