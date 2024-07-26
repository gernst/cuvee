data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure mapsum(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 100000) {
    ret := ret + i + x[i];
    var x₁₀₁₂: int := i;
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
  var i: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁₀₁₃: int;
    __VERIFIER_nondet_int₁₀₁₃ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₁₀₁₃];
    var x₁₀₁₄: int := i;
    i := i + 1;
  }
  var mapsum₁₀₁₅: int;
  mapsum₁₀₁₅ := call mapsum(x);
  ret := mapsum₁₀₁₅;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var mapsum₁₀₁₆: int;
  mapsum₁₀₁₆ := call mapsum(x);
  ret2 := mapsum₁₀₁₆;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 100000 - 1) {
    x := x[i := x[i + 1]];
    var x₁₀₁₇: int := i;
    i := i + 1;
  }
  x := x[100000 - 1 := temp];
  var mapsum₁₀₁₈: int;
  mapsum₁₀₁₈ := call mapsum(x);
  ret5 := mapsum₁₀₁₈;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

