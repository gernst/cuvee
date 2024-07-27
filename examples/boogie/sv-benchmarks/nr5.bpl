data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

var CELLCOUNT: int;

procedure main()
  returns (c#result: int)
  modifies c#heap, CELLCOUNT;
{
  var __VERIFIER_nondet_int₇₅₀: int;
  __VERIFIER_nondet_int₇₅₀ := call __VERIFIER_nondet_int();
  CELLCOUNT := __VERIFIER_nondet_int₇₅₀;
  if(1 < CELLCOUNT) {
    var DEFAULTVALUE: int;
    DEFAULTVALUE := 1;
    var MINVAL: int;
    MINVAL := 2;
    var i: int;
    var j: int;
    var volArray: [int]int;
    if(CELLCOUNT % 5 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 5 == 0;
    i := 1;
    while(i <= CELLCOUNT / 5) {
      j := 5;
      while(1 <= j) {
        if(MINVAL <= j) {
          volArray := volArray[i * 5 - j := j];
        } else {
          volArray := volArray[i * 5 - j := 0];
        }
        var x₇₅₁: int := j;
        j := j - 1;
      }
      var x₇₅₂: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT) {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      var x₇₅₃: int := i;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

