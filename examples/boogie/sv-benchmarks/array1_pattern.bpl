data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure __VERIFIER_nondet_short() returns (c#result: int);
  modifies c#heap;

var ARR_SIZE: int;

procedure main()
  returns (c#result: int)
  modifies c#heap, ARR_SIZE;
{
  var __VERIFIER_nondet_short₁₀₆₃: int;
  __VERIFIER_nondet_short₁₀₆₃ := call __VERIFIER_nondet_short();
  ARR_SIZE := __VERIFIER_nondet_short₁₀₆₃;
  assume 0 < ARR_SIZE;
  var array1: [int]int;
  var array2: [int]int;
  var count: int;
  count := 0;
  var num: int;
  num := -1;
  var temp: int;
  var index: int;
  var sum: int;
  sum := 0;
  count := 0;
  while(count < ARR_SIZE) {
    array1 := array1[count := 0];
    array2 := array2[count := 0];
    var x₁₀₆₄: int := count;
    count := count + 1;
  }
  while(1 != 0) {
    var __VERIFIER_nondet_short₁₀₆₅: int;
    __VERIFIER_nondet_short₁₀₆₅ := call __VERIFIER_nondet_short();
    index := __VERIFIER_nondet_short₁₀₆₅;
    assume 0 <= index && index < ARR_SIZE;
    array1 := array1[index := num * num * index];
    array2 := array2[ARR_SIZE - 1 - index := num * index];
    var __VERIFIER_nondet_int₁₀₆₆: int;
    __VERIFIER_nondet_int₁₀₆₆ := call __VERIFIER_nondet_int();
    temp := __VERIFIER_nondet_int₁₀₆₆;
    if(temp == 0) {
      break;
    }
  }
  count := 0;
  while(count < ARR_SIZE) {
    sum := sum + array1[count] + array2[count];
    var x₁₀₆₇: int := count;
    count := count + 1;
  }
  assert sum == 0;
  c#result := 0;
  return;
}

