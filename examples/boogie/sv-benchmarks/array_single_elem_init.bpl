data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁: int;
    var q: int;
    q := __VERIFIER_nondet_int₁;
    a := a[i := 0];
    if(q == 0) {
      a := a[i := 1];
      b := b[i := i % 2];
    }
    if(a[i] != 0) {
      if(b[i] == 0) {
        c := c[i := 0];
      } else {
        c := c[i := 1];
      }
    }
    i := i + 1;
  }
  a := a[15000 := 1];
  i := 0;
  while(i < 100000) {
    if(i == 15000) {
      assert c[i] == 0;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

