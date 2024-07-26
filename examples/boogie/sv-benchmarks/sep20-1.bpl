data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure sep(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var ret: int;
  ret := 0;
  var i: int;
  i := 0;
  while(i < 20) {
    if(x[i] % 2 == 0) {
      var x₆₈₀: int := ret;
      ret := ret + 1;
    } else {
      var x₆₈₁: int := ret;
      ret := ret - 1;
    }
    var x₆₈₂: int := i;
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
    var __VERIFIER_nondet_int₆₈₃: int;
    __VERIFIER_nondet_int₆₈₃ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₆₈₃];
    var x₆₈₄: int := i;
    i := i + 1;
  }
  var sep₆₈₅: int;
  sep₆₈₅ := call sep(x);
  ret := sep₆₈₅;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₆₈₆: int;
  sep₆₈₆ := call sep(x);
  ret2 := sep₆₈₆;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 20 - 1) {
    x := x[i := x[i + 1]];
    var x₆₈₇: int := i;
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var sep₆₈₈: int;
  sep₆₈₈ := call sep(x);
  ret5 := sep₆₈₈;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

