data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure max(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 40) {
    var x₁₈₄: int;
    if(ret < x[i]) {
      x₁₈₄ := x[i];
    } else {
      x₁₈₄ := ret;
    }
    ret := x₁₈₄;
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
  var max₁₈₆: int;
  max₁₈₆ := call max(x);
  ret := max₁₈₆;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₁₈₇: int;
  max₁₈₇ := call max(x);
  ret2 := max₁₈₇;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 40 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var max₁₈₉: int;
  max₁₈₉ := call max(x);
  ret5 := max₁₈₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

