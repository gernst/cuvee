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
  while(i < 20) {
    var __VERIFIER_nondet_int₃₈₀: int;
    x := x[i := __VERIFIER_nondet_int₃₈₀];
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
  while(i < 20) {
    if(20 / 2 < i) {
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
  var init_nondet₃₈₃: c#void;
  init_nondet₃₈₃ := call init_nondet(x);
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var rangesum₃₈₄: int;
  rangesum₃₈₄ := call rangesum(x);
  ret := rangesum₃₈₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var rangesum₃₈₅: int;
  rangesum₃₈₅ := call rangesum(x);
  ret2 := rangesum₃₈₅;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 20 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var rangesum₃₈₇: int;
  rangesum₃₈₇ := call rangesum(x);
  ret5 := rangesum₃₈₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

