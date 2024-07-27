data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure avg(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 10) {
    ret := ret + x[i];
    var x₅₀₈: int := i;
    i := i + 1;
  }
  c#result := ret / 10;
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
  var avg₅₀₉: int;
  avg₅₀₉ := call avg(x);
  ret := avg₅₀₉;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₅₁₀: int;
  avg₅₁₀ := call avg(x);
  ret2 := avg₅₁₀;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 10 - 1) {
    x := x[i := x[i + 1]];
    var x₅₁₁: int := i;
    i := i + 1;
  }
  x := x[10 - 1 := temp];
  var avg₅₁₂: int;
  avg₅₁₂ := call avg(x);
  ret5 := avg₅₁₂;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

