data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure avg(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 20) {
    ret := ret + x[i];
    var x₄₆₃: int := i;
    i := i + 1;
  }
  c#result := ret / 20;
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
  var avg₄₆₄: int;
  avg₄₆₄ := call avg(x);
  ret := avg₄₆₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₄₆₅: int;
  avg₄₆₅ := call avg(x);
  ret2 := avg₄₆₅;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 20 - 1) {
    x := x[i := x[i + 1]];
    var x₄₆₆: int := i;
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var avg₄₆₇: int;
  avg₄₆₇ := call avg(x);
  ret5 := avg₄₆₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

