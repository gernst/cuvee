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
  while(i < 60) {
    var x₆₀₇: int;
    if(ret < x[i]) {
      x₆₀₇ := x[i];
    } else {
      x₆₀₇ := ret;
    }
    ret := x₆₀₇;
    var x₆₀₈: int := i;
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
  while(i < 60) {
    var __VERIFIER_nondet_int₆₀₉: int;
    __VERIFIER_nondet_int₆₀₉ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₆₀₉];
    var x₆₁₀: int := i;
    i := i + 1;
  }
  var max₆₁₁: int;
  max₆₁₁ := call max(x);
  ret := max₆₁₁;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₆₁₂: int;
  max₆₁₂ := call max(x);
  ret2 := max₆₁₂;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 60 - 1) {
    x := x[i := x[i + 1]];
    var x₆₁₃: int := i;
    i := i + 1;
  }
  x := x[60 - 1 := temp];
  var max₆₁₄: int;
  max₆₁₄ := call max(x);
  ret5 := max₆₁₄;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

