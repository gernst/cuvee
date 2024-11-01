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
  var array: [int][int]int;
  var row: int := 0;
  var column: int := 0;
  var num: int := -1;
  var sum: int := 0;
  row := 0;
  while(row < ARR_SIZE) {
    column := 0;
    while(column < ARR_SIZE) {
      if(column < row) {
        array[row][column] := row + column;
      } else {
        if(row < column) {
          array[row][column] := num * (row + column);
        } else {
          array[row][column] := 0;
        }
      }
      column := column + 1;
    }
    row := row + 1;
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
  assert sum == 0;
  c#result := 0;
  return;
}

