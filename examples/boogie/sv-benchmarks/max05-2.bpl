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
  while(i < 5) {
    var x₅₉: int;
    if(ret < x[i]) {
      x₅₉ := x[i];
    } else {
      x₅₉ := ret;
    }
    ret := x₅₉;
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
  var max₆₁: int;
  max₆₁ := call max(x);
  ret := max₆₁;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₆₂: int;
  max₆₂ := call max(x);
  ret2 := max₆₂;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 5 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var max₆₄: int;
  max₆₄ := call max(x);
  ret5 := max₆₄;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

