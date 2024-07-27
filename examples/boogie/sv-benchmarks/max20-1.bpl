data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure max(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 20) {
    var x₅₃₂: int;
    if(ret < x[i]) {
      x₅₃₂ := x[i];
    } else {
      x₅₃₂ := ret;
    }
    ret := x₅₃₂;
    var x₅₃₃: int := i;
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
  while(i < 20) {
    var __VERIFIER_nondet_int₅₃₄: int;
    __VERIFIER_nondet_int₅₃₄ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₅₃₄];
    var x₅₃₅: int := i;
    i := i + 1;
  }
  var max₅₃₆: int;
  max₅₃₆ := call max(x);
  ret := max₅₃₆;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₅₃₇: int;
  max₅₃₇ := call max(x);
  ret2 := max₅₃₇;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 20 - 1) {
    x := x[i := x[i + 1]];
    var x₅₃₈: int := i;
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var max₅₃₉: int;
  max₅₃₉ := call max(x);
  ret5 := max₅₃₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

