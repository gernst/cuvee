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
  var __VERIFIER_nondet_short₁₀₅₆: int;
  ARR_SIZE := __VERIFIER_nondet_short₁₀₅₆;
  assume 0 < ARR_SIZE;
  var array1: [int]int;
  var array2: [int]int;
  var count: int;
  count := 0;
  var num: int;
  num := -1;
  var sum: int;
  sum := 0;
  var temp: int;
  var index1: int;
  var index2: int;
  count := 0;
  while(count < ARR_SIZE) {
    array1 := array1[count := 0];
    array2 := array2[count := 0];
    count := count + 1;
  }
  count := 1;
  while(1 != 0) {
    var __VERIFIER_nondet_short₁₀₅₈: int;
    index1 := __VERIFIER_nondet_short₁₀₅₈;
    var __VERIFIER_nondet_short₁₀₅₉: int;
    index2 := __VERIFIER_nondet_short₁₀₅₉;
    assume 0 <= index1 && index1 < ARR_SIZE;
    assume 0 <= index2 && index2 < ARR_SIZE;
    assume array1[index1] == 0;
    assume array2[index2] == 0;
    array1 := array1[index1 := num * num * count];
    array2 := array2[index2 := num * count];
    if(count == 200) {
      count := 0;
    }
    count := count + 1;
    var __VERIFIER_nondet_int₁₀₆₁: int;
    temp := __VERIFIER_nondet_int₁₀₆₁;
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

