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
  while(i < 5) {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret / 5;
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
  var avg₁₁₉: int;
  avg₁₁₉ := call avg(x);
  ret := avg₁₁₉;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₁₂₀: int;
  avg₁₂₀ := call avg(x);
  ret2 := avg₁₂₀;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 5 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var avg₁₂₂: int;
  avg₁₂₂ := call avg(x);
  ret5 := avg₁₂₂;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

