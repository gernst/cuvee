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
  while(i < 100) {
    ret := ret + i + x[i];
    var x₈₁₀: int := i;
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
  while(i < 100) {
    var __VERIFIER_nondet_int₈₁₁: int;
    __VERIFIER_nondet_int₈₁₁ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₈₁₁];
    var x₈₁₂: int := i;
    i := i + 1;
  }
  var mapsum₈₁₃: int;
  mapsum₈₁₃ := call mapsum(x);
  ret := mapsum₈₁₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var mapsum₈₁₄: int;
  mapsum₈₁₄ := call mapsum(x);
  ret2 := mapsum₈₁₄;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 100 - 1) {
    x := x[i := x[i + 1]];
    var x₈₁₅: int := i;
    i := i + 1;
  }
  x := x[100 - 1 := temp];
  var mapsum₈₁₆: int;
  mapsum₈₁₆ := call mapsum(x);
  ret5 := mapsum₈₁₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

