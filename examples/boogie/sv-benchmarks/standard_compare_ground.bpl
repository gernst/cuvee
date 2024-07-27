data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var a: [int]int;
  var b: [int]int;
  var j: int;
  j := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₁₈₆: int;
    __VERIFIER_nondet_int₁₈₆ := call __VERIFIER_nondet_int();
    a := a[j := __VERIFIER_nondet_int₁₈₆];
    var __VERIFIER_nondet_int₁₈₇: int;
    __VERIFIER_nondet_int₁₈₇ := call __VERIFIER_nondet_int();
    b := b[j := __VERIFIER_nondet_int₁₈₇];
    var x₁₈₈: int := j;
    j := j + 1;
  }
  var i: int;
  i := 0;
  var rv: int;
  rv := 1;
  while(i < 100000) {
    if(a[i] != b[i]) {
      rv := 0;
    }
    i := i + 1;
  }
  if(rv != 0) {
    var x: int;
    x := 0;
    while(x < 100000) {
      assert a[x] == b[x];
      var x₁₈₉: int := x;
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

