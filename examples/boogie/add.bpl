function inv(x0: int, y0: int, x: int, y: int): bool {
  0 <= x && x0 + y0 == x + y
}

procedure add(x0: int, y0: int)
  returns (s: int)
  requires 0 <= x0;
  ensures s == x0 + y0;
{
  var x: int, y: int := x0, y0;

  while(x > 0)
    decreases x;
    invariant inv(x0,y0,x,y);
  {
    x := x - 1;
    y := y + 1;
  }

  s := y;
}
