// Harder versions of some of the properties from partition-example
// 1) each element in b is a copy of some element in a, which fulfils the range-bounds of a
// 2) each element in c is a copy of some element in a, which fulfils the range-bounds of a
// 3) for each element in a, which is greater or equal 0, there exists a copy of that element in b, which fulfils the range-bounds of b
// 4) for each element in a, which is smaller than 0, there exists a copy of that element in c, which fulfils the range-bounds of c
// 5) for each element in a, either there exists a copy of that element in b, which fulfils the range-bounds of b, or there exists a copy of that element in c, which fulfils the range-bounds of c

procedure partition_harder(a: [int]int, alength: int)
  returns (b: [int]int, c: [int]int, blength: int , clength: int)
  requires 0 <= alength;
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < blength ==>
    (exists pos2: int :: 0 <= pos2 && pos2 < alength && b[pos] == a[pos2]);
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < clength ==>
    (exists pos2: int :: 0 <= pos2 && pos2 < alength && c[pos] == a[pos2]);
  ensures forall pos: int :: 
    0 <= alength && 0 <= pos && pos < alength && 0 <= a[pos] ==>
      (exists pos2: int :: 0 <= pos2 && pos2 < blength && b[pos2] == a[pos]);
  ensures forall pos: int :: 
    0 <= alength && 0 <= pos && pos < alength && a[pos] < 0 ==>
      (exists pos2: int :: 0 <= pos2 && pos2 < clength && c[pos2] == a[pos]);
  ensures forall pos: int :: 0 <= alength && 0 <= pos && pos < alength ==>
    ((exists pos2: int :: 0 <= pos2 && pos2 < blength && b[pos2] == a[pos]) ||
      (exists pos2: int :: 0 <= pos2 && pos2 < clength && c[pos2] == a[pos]));
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
