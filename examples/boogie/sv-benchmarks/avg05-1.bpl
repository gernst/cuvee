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
  var i: int;
  i := 0;
  while(i < 5) {
    var __VERIFIER_nondet_int₅₀₂: int;
    x := x[i := __VERIFIER_nondet_int₅₀₂];
    i := i + 1;
  }
  var avg₅₀₄: int;
  avg₅₀₄ := call avg(x);
  ret := avg₅₀₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₅₀₅: int;
  avg₅₀₅ := call avg(x);
  ret2 := avg₅₀₅;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 5 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var avg₅₀₇: int;
  avg₅₀₇ := call avg(x);
  ret5 := avg₅₀₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

