data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure avg(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 40) {
    ret := ret + x[i];
    var x₅₈₁: int := i;
    i := i + 1;
  }
  c#result := ret / 40;
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
  while(i < 40) {
    var __VERIFIER_nondet_int₅₈₂: int;
    __VERIFIER_nondet_int₅₈₂ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₅₈₂];
    var x₅₈₃: int := i;
    i := i + 1;
  }
  var avg₅₈₄: int;
  avg₅₈₄ := call avg(x);
  ret := avg₅₈₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₅₈₅: int;
  avg₅₈₅ := call avg(x);
  ret2 := avg₅₈₅;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 40 - 1) {
    x := x[i := x[i + 1]];
    var x₅₈₆: int := i;
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var avg₅₈₇: int;
  avg₅₈₇ := call avg(x);
  ret5 := avg₅₈₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

