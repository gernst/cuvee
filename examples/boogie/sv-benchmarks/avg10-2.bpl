data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure avg(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 10) {
    ret := ret + x[i];
    i := i + 1;
  }
  c#result := ret / 10;
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
    var __VERIFIER_nondet_int₆₁₆: int;
    x := x[i := __VERIFIER_nondet_int₆₁₆];
    i := i + 1;
  }
  var avg₆₁₈: int;
  avg₆₁₈ := call avg(x);
  ret := avg₆₁₈;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₆₁₉: int;
  avg₆₁₉ := call avg(x);
  ret2 := avg₆₁₉;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 10 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[10 - 1 := temp];
  var avg₆₂₁: int;
  avg₆₂₁ := call avg(x);
  ret5 := avg₆₂₁;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

