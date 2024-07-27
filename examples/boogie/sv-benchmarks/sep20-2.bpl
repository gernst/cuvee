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
  while(i < 20) {
    if(x[i] % 2 == 0) {
      var x₅₁₃: int := ret;
      ret := ret + 1;
    } else {
      var x₅₁₄: int := ret;
      ret := ret - 1;
    }
    var x₅₁₅: int := i;
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
  var sep₅₁₆: int;
  sep₅₁₆ := call sep(x);
  ret := sep₅₁₆;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₅₁₇: int;
  sep₅₁₇ := call sep(x);
  ret2 := sep₅₁₇;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 20 - 1) {
    x := x[i := x[i + 1]];
    var x₅₁₈: int := i;
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var sep₅₁₉: int;
  sep₅₁₉ := call sep(x);
  ret5 := sep₅₁₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

