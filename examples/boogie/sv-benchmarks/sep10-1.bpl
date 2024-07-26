data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure sep(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var ret: int;
  ret := 0;
  var i: int;
  i := 0;
  while(i < 10) {
    if(x[i] % 2 == 0) {
      var x₃₈₈: int := ret;
      ret := ret + 1;
    } else {
      var x₃₈₉: int := ret;
      ret := ret - 1;
    }
    var x₃₉₀: int := i;
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
  var sep₃₉₁: int;
  sep₃₉₁ := call sep(x);
  ret := sep₃₉₁;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₃₉₂: int;
  sep₃₉₂ := call sep(x);
  ret2 := sep₃₉₂;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 10 - 1) {
    x := x[i := x[i + 1]];
    var x₃₉₃: int := i;
    i := i + 1;
  }
  x := x[10 - 1 := temp];
  var sep₃₉₄: int;
  sep₃₉₄ := call sep(x);
  ret5 := sep₃₉₄;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

