data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure sum(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 10) {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret;
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
  var sum₇₇: int;
  sum₇₇ := call sum(x);
  ret := sum₇₇;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sum₇₈: int;
  sum₇₈ := call sum(x);
  ret2 := sum₇₈;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 10 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[10 - 1 := temp];
  var sum₈₀: int;
  sum₈₀ := call sum(x);
  ret5 := sum₈₀;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

