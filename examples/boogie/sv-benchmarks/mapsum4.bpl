data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure mapsum(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 100000) {
    ret := ret + i + x[i];
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
  var i: int := 0;
  while(i < 100000) {
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    x[i] := nondet_int₂;
    i := i + 1;
  }
  var mapsum₄: int;
  mapsum₄ := call mapsum(x);
  ret := mapsum₄;
  temp := x[0];
  x[0] := x[1];
  x[1] := temp;
  var mapsum₅: int;
  mapsum₅ := call mapsum(x);
  ret2 := mapsum₅;
  temp := x[0];
  var i: int := 0;
  while(i < 100000 - 1) {
    x[i] := x[i + 1];
    i := i + 1;
  }
  x[(100000 - 1)] := temp;
  var mapsum₇: int;
  mapsum₇ := call mapsum(x);
  ret5 := mapsum₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

