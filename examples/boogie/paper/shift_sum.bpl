// ./Cuvee.sh examples/boogie/paper/shift_sum.bpl -annotate:traces -vcgen:partial -split -simplify2
procedure sum(x: [int]int)
  returns (r: int)
{
  var i: int := 0;
  r := 0;
  while(i < 5) {
    r := r + x[i];
    i := i + 1;
  }
}

procedure main()
  returns (x: [int]int)
  // requires 1 < n;
{
  var i: int := 0;

  // sum over original array
  var ret: int;
  ret := call sum(x);

  // swap and sum 
  var temp: int;
  temp := x[0];
  x[0] := x[1];
  x[1] := temp;
  var sum₅: int;
  sum₅ := call sum(x);
  var ret2: int := sum₅;

  // shift with loop
  temp := x[0];
  var i: int := 0;
  while(i < 5 - 1) {
    x[i] := x[i + 1];
    i := i + 1;
  }
  x[(5 - 1)] := temp;

  // sum
  var ret5: int;
  ret5 := call sum(x);

  // assert ret == ret2;

  // assert ret == ret5;

  if(ret != ret2 || ret != ret5) {
    assert false;
  }
}

