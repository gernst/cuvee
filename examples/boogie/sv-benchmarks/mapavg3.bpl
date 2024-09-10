data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure mapavg(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 10000) {
    ret := ret + i + x[i];
    i := i + 1;
  }
  c#result := ret / 10000;
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
  var i: int := 0;
  while(i < 10000) {
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    x := x[i := nondet_int₂];
    i := i + 1;
  }
  var mapavg₄: int;
  mapavg₄ := call mapavg(x);
  ret := mapavg₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var mapavg₅: int;
  mapavg₅ := call mapavg(x);
  ret2 := mapavg₅;
  temp := x[0];
  var i: int := 0;
  while(i < 10000 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[10000 - 1 := temp];
  var mapavg₇: int;
  mapavg₇ := call mapavg(x);
  ret5 := mapavg₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

