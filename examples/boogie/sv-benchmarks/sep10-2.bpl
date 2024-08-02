data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure sep(x: [int]int)
  returns (c#result: int)
{
  var ret: int;
  ret := 0;
  var i: int;
  i := 0;
  while(i < 10) {
    if(x[i] % 2 == 0) {
      ret := ret + 1;
    } else {
      ret := ret - 1;
    }
    i := i + 1;
  }
  c#result := ret;
  return;
}

procedure main()
  returns (c#result: int)
{
  var x: [int]int;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var i: int;
  i := 0;
  while(i < 10) {
    var __VERIFIER_nondet_int₄₁₅: int;
    x := x[i := __VERIFIER_nondet_int₄₁₅];
    i := i + 1;
  }
  var sep₄₁₇: int;
  sep₄₁₇ := call sep(x);
  ret := sep₄₁₇;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₄₁₈: int;
  sep₄₁₈ := call sep(x);
  ret2 := sep₄₁₈;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 10 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[10 - 1 := temp];
  var sep₄₂₀: int;
  sep₄₂₀ := call sep(x);
  ret5 := sep₄₂₀;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

