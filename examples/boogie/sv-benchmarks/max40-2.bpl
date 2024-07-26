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
  while(i < 40) {
    var x₆₉₇: int;
    if(ret < x[i]) {
      x₆₉₇ := x[i];
    } else {
      x₆₉₇ := ret;
    }
    ret := x₆₉₇;
    var x₆₉₈: int := i;
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
  var max₆₉₉: int;
  max₆₉₉ := call max(x);
  ret := max₆₉₉;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₇₀₀: int;
  max₇₀₀ := call max(x);
  ret2 := max₇₀₀;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 40 - 1) {
    x := x[i := x[i + 1]];
    var x₇₀₁: int := i;
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var max₇₀₂: int;
  max₇₀₂ := call max(x);
  ret5 := max₇₀₂;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

