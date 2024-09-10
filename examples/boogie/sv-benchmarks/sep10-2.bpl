data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure sep(x: [int]int)
  returns (c#result: int)
{
  var ret: int := 0;
  var i: int := 0;
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
  var i: int := 0;
  while(i < 10) {
    var nondet_int₄: int;
    assume -2147483648 <= nondet_int₄ && nondet_int₄ < 2147483648;
    x[i] := nondet_int₄;
    i := i + 1;
  }
  var sep₆: int;
  sep₆ := call sep(x);
  ret := sep₆;
  temp := x[0];
  x[0] := x[1];
  x[1] := temp;
  var sep₇: int;
  sep₇ := call sep(x);
  ret2 := sep₇;
  temp := x[0];
  var i: int := 0;
  while(i < 10 - 1) {
    x[i] := x[i + 1];
    i := i + 1;
  }
  x[(10 - 1)] := temp;
  var sep₉: int;
  sep₉ := call sep(x);
  ret5 := sep₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

