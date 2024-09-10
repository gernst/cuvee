data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var ARR_SIZE: int;

procedure main()
  returns (c#result: int)
  modifies ARR_SIZE;
{
  ARR_SIZE := 0;
  var nondet_short₁: int;
  assume -32768 <= nondet_short₁ && nondet_short₁ < 32768;
  ARR_SIZE := nondet_short₁;
  assume 0 < ARR_SIZE;
  var array1: [int]int;
  var array2: [int]int;
  var count: int := 0;
  var num: int := -1;
  var sum: int := 0;
  var temp: int;
  var index: int;
  count := 0;
  while(count < ARR_SIZE) {
    array1[count] := 0;
    array2[count] := 0;
    count := count + 1;
  }
  count := 1;
  while(1 != 0) {
    havoc index;
    assume -32768 <= index && index < 32768;
    assume 0 <= index && index < ARR_SIZE;
    if(index % 2 == 0) {
      array1[index] := num * num * count;
      array2[index] := num * count;
    } else {
      array1[index] := num * count;
      array2[index] := num * num * count;
    }
    if(count == 200) {
      count := 0;
    }
    count := count + 1;
    havoc temp;
    assume -2147483648 <= temp && temp < 2147483648;
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

