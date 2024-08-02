data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure avg(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < N) {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret / N;
  return;
}

procedure main()
  returns (c#result: int)
  modifies N;
{
  var __VERIFIER_nondet_int₄₅₈: int;
  N := __VERIFIER_nondet_int₄₅₈;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var avg₄₅₉: int;
    avg₄₅₉ := call avg(x);
    ret := avg₄₅₉;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var avg₄₆₀: int;
    avg₄₆₀ := call avg(x);
    ret2 := avg₄₆₀;
    temp := x[0];
    var i: int;
    i := 0;
    while(i < N - 1) {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var avg₄₆₂: int;
    avg₄₆₂ := call avg(x);
    ret5 := avg₄₆₂;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

