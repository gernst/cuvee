data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var ARR_SIZE: int;

procedure outerBoundaryPatternCheck(index: int)
  returns (c#result: int)
  modifies ARR_SIZE;
{
  if(index == 0 || index == ARR_SIZE - 1) {
    c#result := 1;
    return;
  } else {
    c#result := 0;
    return;
  }
}

procedure main()
  returns (c#result: int)
  modifies ARR_SIZE;
{
  ARR_SIZE := 0;
  var nondet_short₁: int;
  ARR_SIZE := nondet_short₁;
  assume 1 < ARR_SIZE;
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
      array[row][column] := 0;
      column := column + 1;
    }
    row := row + 1;
  }
  while(1 != 0) {
    havoc index1;
    havoc index2;
    assume 0 <= index1 && index1 < ARR_SIZE;
    assume 0 <= index2 && index2 < ARR_SIZE;
    var outerBoundaryPatternCheck₄: int;
    outerBoundaryPatternCheck₄ := call outerBoundaryPatternCheck(index1);
    var x₆: bool := outerBoundaryPatternCheck₄ != 0;
    if(!(x₆)) {
      var outerBoundaryPatternCheck₅: int;
      outerBoundaryPatternCheck₅ := call outerBoundaryPatternCheck(index2);
      x₆ := outerBoundaryPatternCheck₅ != 0;
    }
    var x₇: int;
    if(x₆) {
      x₇ := num * num;
    } else {
      x₇ := array[index1][index2];
    }
    array[index1][index2] := x₇;
    havoc temp;
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
  assert sum <= 4 * (ARR_SIZE - 1);
  c#result := 0;
  return;
}

