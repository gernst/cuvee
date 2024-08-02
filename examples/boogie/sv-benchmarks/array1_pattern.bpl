data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var ARR_SIZE: int;

procedure main()
  returns (c#result: int)
  modifies ARR_SIZE;
{
  var __VERIFIER_nondet_short₁₀₆₃: int;
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
    count := count + 1;
  }
  while(1 != 0) {
    var __VERIFIER_nondet_short₁₀₆₅: int;
    index := __VERIFIER_nondet_short₁₀₆₅;
    assume 0 <= index && index < ARR_SIZE;
    array1 := array1[index := num * num * index];
    array2 := array2[ARR_SIZE - 1 - index := num * index];
    var __VERIFIER_nondet_int₁₀₆₆: int;
    temp := __VERIFIER_nondet_int₁₀₆₆;
    if(temp == 0) {
      break;
    }
  }
  count := 0;
  while(count < ARR_SIZE) {
    sum := sum + array1[count] + array2[count];
    count := count + 1;
  }
  assert sum == 0;
  c#result := 0;
  return;
}

