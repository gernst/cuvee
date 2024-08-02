data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure avg(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 60) {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret / 60;
  return;
}

procedure main()
  returns (c#result: int)
{
  var x: [int]int;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var avg₇₂: int;
  avg₇₂ := call avg(x);
  ret := avg₇₂;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₇₃: int;
  avg₇₃ := call avg(x);
  ret2 := avg₇₃;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 60 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[60 - 1 := temp];
  var avg₇₅: int;
  avg₇₅ := call avg(x);
  ret5 := avg₇₅;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

