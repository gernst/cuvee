data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure xor(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < 100000) {
    res := c#bitxor(res, x[i]);
    i := i + 1;
  }
  c#result := res;
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
  var xor₄: int;
  xor₄ := call xor(x);
  ret := xor₄;
  temp := x[0];
  x[0] := x[1];
  x[1] := temp;
  var xor₅: int;
  xor₅ := call xor(x);
  ret2 := xor₅;
  temp := x[0];
  var i: int := 0;
  while(i < 100000 - 1) {
    x[i] := x[i + 1];
    i := i + 1;
  }
  x[(100000 - 1)] := temp;
  var xor₇: int;
  xor₇ := call xor(x);
  ret5 := xor₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

