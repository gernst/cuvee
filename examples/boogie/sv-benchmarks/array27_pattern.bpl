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
  var sum: int := 0;
  row := 0;
  while(row < ARR_SIZE) {
    column := 0;
    while(column < ARR_SIZE) {
      if(row == column) {
        array[row][row] := 0;
      } else {
        array[row][column] := row;
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
  assert 2 * sum == ARR_SIZE * (ARR_SIZE - 1) * (ARR_SIZE - 1);
  c#result := 0;
  return;
}

