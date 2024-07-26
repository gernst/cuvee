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
  var __VERIFIER_nondet_int₇₃₈: int;
  __VERIFIER_nondet_int₇₃₈ := call __VERIFIER_nondet_int();
  CELLCOUNT := __VERIFIER_nondet_int₇₃₈;
  if(1 < CELLCOUNT) {
    var MINVAL: int;
    var i: int;
    var volArray: [int]int;
    var CCCELVOL3: int;
    CCCELVOL3 := 7;
    var CCCELVOL2: int;
    CCCELVOL2 := 3;
    var CCCELVOL1: int;
    CCCELVOL1 := 1;
    if(CELLCOUNT % 3 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 3 == 0;
    i := 1;
    while(i <= CELLCOUNT / 3) {
      if(MINVAL <= CCCELVOL3) {
        volArray := volArray[i * 3 - 3 := CCCELVOL3];
      } else {
        volArray := volArray[i * 3 - 3 := 0];
      }
      if(MINVAL <= CCCELVOL2) {
        volArray := volArray[i * 3 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 3 - 2 := 0];
      }
      if(MINVAL <= CCCELVOL1) {
        volArray := volArray[i * 3 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 3 - 1 := 0];
      }
      var x₇₃₉: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT) {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      var x₇₄₀: int := i;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

