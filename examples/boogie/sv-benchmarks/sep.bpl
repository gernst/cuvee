data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure sep(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var ret: int := 0;
  var i: int := 0;
  while(i < N) {
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
  modifies N;
{
  N := 0;
  havoc N;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var sep₄: int;
    sep₄ := call sep(x);
    ret := sep₄;
    temp := x[0];
    x[0] := x[1];
    x[1] := temp;
    var sep₅: int;
    sep₅ := call sep(x);
    ret2 := sep₅;
    temp := x[0];
    var i: int := 0;
    while(i < N - 1) {
      x[i] := x[i + 1];
      i := i + 1;
    }
    x[(N - 1)] := temp;
    var sep₇: int;
    sep₇ := call sep(x);
    ret5 := sep₇;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

