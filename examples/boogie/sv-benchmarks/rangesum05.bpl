data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure init_nondet(x: [int]int)
  returns (c#result: c#void)
{
  var i: int;
  i := 0;
  while(i < 5) {
    var __VERIFIER_nondet_int₆₈₉: int;
    x := x[i := __VERIFIER_nondet_int₆₈₉];
    i := i + 1;
  }
}

procedure rangesum(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  var cnt: int;
  cnt := 0;
  i := 0;
  while(i < 5) {
    if(5 / 2 < i) {
      ret := ret + x[i];
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  if(cnt != 0) {
    c#result := ret / cnt;
    return;
  } else {
    c#result := 0;
    return;
  }
}

procedure main()
  returns (c#result: int)
{
  var x: [int]int;
  var init_nondet₆₉₂: c#void;
  init_nondet₆₉₂ := call init_nondet(x);
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var rangesum₆₉₃: int;
  rangesum₆₉₃ := call rangesum(x);
  ret := rangesum₆₉₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var rangesum₆₉₄: int;
  rangesum₆₉₄ := call rangesum(x);
  ret2 := rangesum₆₉₄;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 5 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var rangesum₆₉₆: int;
  rangesum₆₉₆ := call rangesum(x);
  ret5 := rangesum₆₉₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

