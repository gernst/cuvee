data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var j: int;
  j := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₁₈₆: int;
    a := a[j := __VERIFIER_nondet_int₁₈₆];
    var __VERIFIER_nondet_int₁₈₇: int;
    b := b[j := __VERIFIER_nondet_int₁₈₇];
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
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

