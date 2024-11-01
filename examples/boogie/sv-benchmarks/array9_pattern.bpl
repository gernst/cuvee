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
    assume 0 <= index && index < ARR_SIZE;
    array1[index] := num * num * count;
    var x₃: int;
    if(index % 3 == 0) {
      x₃ := array2[index];
    } else {
      x₃ := num * count;
    }
    array2[index] := x₃;
    havoc temp;
    if(temp == 0) {
      break;
    }
  }
  count := 0;
  while(count < ARR_SIZE) {
    sum := sum + array1[count] + array2[count];
    count := count + 1;
  }
  assert 3 * sum <= ARR_SIZE + 2;
  c#result := 0;
  return;
}

