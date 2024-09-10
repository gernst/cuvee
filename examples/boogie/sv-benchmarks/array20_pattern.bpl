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
  var array: [int][int]int;
  var row: int := 0;
  var column: int := 0;
  var num: int := -1;
  var sum: int := 0;
  var temp: int;
  var index1: int;
  var index2: int;
  row := 0;
  while(row < ARR_SIZE) {
    column := 0;
    while(column < ARR_SIZE) {
      array := array[row := array[row][column := 0]];
      column := column + 1;
    }
    row := row + 1;
  }
  while(1 != 0) {
    var nondet_short₄: int;
    assume -32768 <= nondet_short₄ && nondet_short₄ < 32768;
    index1 := nondet_short₄;
    var nondet_short₅: int;
    assume -32768 <= nondet_short₅ && nondet_short₅ < 32768;
    index2 := nondet_short₅;
    assume 0 <= index1 && index1 < ARR_SIZE;
    assume 0 <= index2 && index2 < ARR_SIZE;
    var x₆: int;
    if(index1 + index2 == ARR_SIZE - 1) {
      x₆ := num;
    } else {
      x₆ := array[index1][index2];
    }
    array := array[index1 := array[index1][index2 := x₆]];
    var x₇: int;
    if(index1 + index2 == ARR_SIZE - 1) {
      x₇ := num * num * num * num;
    } else {
      x₇ := array[ARR_SIZE - 1 - index1][index2];
    }
    array := array[ARR_SIZE - 1 - index1 := array[ARR_SIZE - 1 - index1][index2 := x₇]];
    havoc temp;
    assume -2147483648 <= temp && temp < 2147483648;
    if(temp == 0) {
      break;
    }
  }
  row := 0;
  while(row < ARR_SIZE) {
    column := 0;
    while(column < ARR_SIZE) {
      sum := sum + array[row][column];
      column := column + 1;
    }
    row := row + 1;
  }
  assert sum == 0 || sum == 1;
  c#result := 0;
  return;
}

