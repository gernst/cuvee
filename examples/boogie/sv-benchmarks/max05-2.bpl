data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure max(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 5) {
    var x₄₂₁: int;
    if(ret < x[i]) {
      x₄₂₁ := x[i];
    } else {
      x₄₂₁ := ret;
    }
    ret := x₄₂₁;
    var x₄₂₂: int := i;
    i := i + 1;
  }
  c#result := ret;
  return;
}

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var x: [int]int;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var max₄₂₃: int;
  max₄₂₃ := call max(x);
  ret := max₄₂₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₄₂₄: int;
  max₄₂₄ := call max(x);
  ret2 := max₄₂₄;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 5 - 1) {
    x := x[i := x[i + 1]];
    var x₄₂₅: int := i;
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var max₄₂₆: int;
  max₄₂₆ := call max(x);
  ret5 := max₄₂₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

