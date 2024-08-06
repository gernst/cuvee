var SIZE: int;
procedure main()
  modifies SIZE;
{
  havoc SIZE;
  var i: int;
  {
    var i: int := 0;
    while(i < SIZE)
    {
      i := i + 1;
    }
  }
}