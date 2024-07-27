data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure sum(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 40) {
    ret := ret + x[i];
    var x₄₂₇: int := i;
    i := i + 1;
  }
  c#result := ret;
  return;
}

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var x: [int]int;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var sum₄₂₈: int;
  sum₄₂₈ := call sum(x);
  ret := sum₄₂₈;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sum₄₂₉: int;
  sum₄₂₉ := call sum(x);
  ret2 := sum₄₂₉;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 40 - 1) {
    x := x[i := x[i + 1]];
    var x₄₃₀: int := i;
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var sum₄₃₁: int;
  sum₄₃₁ := call sum(x);
  ret5 := sum₄₃₁;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

