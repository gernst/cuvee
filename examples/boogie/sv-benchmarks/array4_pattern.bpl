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
  havoc ARR_SIZE;
  assume 0 < ARR_SIZE;
  var array1: [int]int;
  var array2: [int]int;
  var count: int := 0;
  var num: int := -1;
  var sum: int := 0;
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
    havoc index1;
    havoc index2;
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
  assert sum == 0;
  c#result := 0;
  return;
}

