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
    array1 := array1[count := 0];
    array2 := array2[count := 0];
    count := count + 1;
  }
  while(1 != 0) {
    var nondet_short₃: int;
    assume -32768 <= nondet_short₃ && nondet_short₃ < 32768;
    index := nondet_short₃;
    assume 0 <= index && index < ARR_SIZE;
    array1 := array1[index := num * num * num * num * index];
    var x₄: int;
    if(index % 2 != 0) {
      x₄ := num * index;
    } else {
      x₄ := array2[index];
    }
    array2 := array2[index := x₄];
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
  assert 4 * sum <= (ARR_SIZE - 1) * (ARR_SIZE + 1);
  c#result := 0;
  return;
}

