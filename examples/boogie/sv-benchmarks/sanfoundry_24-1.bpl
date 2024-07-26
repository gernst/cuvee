data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure printEven(i: int)
  returns (c#result: c#void)
  modifies c#heap;
{
  assert i % 2 == 0;
}

procedure printOdd(i: int)
  returns (c#result: c#void)
  modifies c#heap;
{
  assert i % 2 != 0;
}

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var array: [int]int;
  var i: int;
  var __VERIFIER_nondet_int₈₆: int;
  __VERIFIER_nondet_int₈₆ := call __VERIFIER_nondet_int();
  var num: int;
  num := __VERIFIER_nondet_int₈₆;
  i := 0;
  while(i < num) {
    var __VERIFIER_nondet_int₈₇: int;
    __VERIFIER_nondet_int₈₇ := call __VERIFIER_nondet_int();
    array := array[i := __VERIFIER_nondet_int₈₇];
    var x₈₈: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < num) {
    if(array[i] % 2 == 0) {
      var printEven₈₉: c#void;
      printEven₈₉ := call printEven(array[i]);
    }
    var x₉₀: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < num) {
    if(array[i] % 2 != 0) {
      var printOdd₉₁: c#void;
      printOdd₉₁ := call printOdd(array[i]);
    }
    var x₉₂: int := i;
    i := i + 1;
  }
  c#result := 0;
  return;
}

