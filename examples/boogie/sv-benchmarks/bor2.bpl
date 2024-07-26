data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure bor(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < 1000) {
    res := c#bitor(res, x[i]);
    var x₈₈₃: int := i;
    i := i + 1;
  }
  c#result := res;
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
  while(i < 1000) {
    var __VERIFIER_nondet_int₈₈₄: int;
    __VERIFIER_nondet_int₈₈₄ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₈₈₄];
    var x₈₈₅: int := i;
    i := i + 1;
  }
  var bor₈₈₆: int;
  bor₈₈₆ := call bor(x);
  ret := bor₈₈₆;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bor₈₈₇: int;
  bor₈₈₇ := call bor(x);
  ret2 := bor₈₈₇;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 1000 - 1) {
    x := x[i := x[i + 1]];
    var x₈₈₈: int := i;
    i := i + 1;
  }
  x := x[1000 - 1 := temp];
  var bor₈₈₉: int;
  bor₈₈₉ := call bor(x);
  ret5 := bor₈₈₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

