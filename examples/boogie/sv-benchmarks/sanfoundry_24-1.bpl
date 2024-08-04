data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure printEven(i: int)
  returns (c#result: c#void)
{
  assert i % 2 == 0;
}

procedure printOdd(i: int)
  returns (c#result: c#void)
{
  assert i % 2 != 0;
}

procedure main()
  returns (c#result: int)
{
  var array: [int]int;
  var i: int;
  var __VERIFIER_nondet_int₁: int;
  var num: int;
  num := __VERIFIER_nondet_int₁;
  i := 0;
  while(i < num) {
    var __VERIFIER_nondet_int₂: int;
    array := array[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < num) {
    if(array[i] % 2 == 0) {
      var printEven₄: c#void;
      printEven₄ := call printEven(array[i]);
    }
    i := i + 1;
  }
  i := 0;
  while(i < num) {
    if(array[i] % 2 != 0) {
      var printOdd₆: c#void;
      printOdd₆ := call printOdd(array[i]);
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

