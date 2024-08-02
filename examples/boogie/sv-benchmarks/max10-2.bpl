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
  while(i < 10) {
    var x₅₉₆: int;
    if(ret < x[i]) {
      x₅₉₆ := x[i];
    } else {
      x₅₉₆ := ret;
    }
    ret := x₅₉₆;
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
  var max₅₉₈: int;
  max₅₉₈ := call max(x);
  ret := max₅₉₈;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₅₉₉: int;
  max₅₉₉ := call max(x);
  ret2 := max₅₉₉;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 10 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[10 - 1 := temp];
  var max₆₀₁: int;
  max₆₀₁ := call max(x);
  ret5 := max₆₀₁;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

