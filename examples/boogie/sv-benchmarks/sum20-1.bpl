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
  while(i < 20) {
    ret := ret + x[i];
    var x₆₀₂: int := i;
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
  var sum₆₀₃: int;
  sum₆₀₃ := call sum(x);
  ret := sum₆₀₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sum₆₀₄: int;
  sum₆₀₄ := call sum(x);
  ret2 := sum₆₀₄;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 20 - 1) {
    x := x[i := x[i + 1]];
    var x₆₀₅: int := i;
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var sum₆₀₆: int;
  sum₆₀₆ := call sum(x);
  ret5 := sum₆₀₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

