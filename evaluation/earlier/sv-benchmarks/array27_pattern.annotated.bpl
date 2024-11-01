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
  var sum: int := 0;
  row := 0;
  while(row < ARR_SIZE)
    decreases ARR_SIZE - row;
    invariant old(row) <= row
      && (forall row₇: int ::
            (  old(row) <= row₇
              && row₇ < row
               ==> (exists array₄: [int][int]int, column₅: int ::
                      0 <= column₅
                      && (forall column₃: int ::
                            (  0 <= column₃
                              && column₃ < column₅
                               ==> row₇ == column₃
                                  && column₃ < ARR_SIZE
                                  && array₄[row₇][row₇] == 0
                                ||   row₇ != column₃
                                  && column₃ < ARR_SIZE
                                  && array₄[row₇][column₃] == row₇))
                      && (forall column₃: int ::
                            (!(  0 <= column₃
                              && column₃ < column₅
                            )
                               ==> array₄[row₇][row₇] == array[row₇][row₇]
                                && array₄[row₇][column₃] == array[row₇][column₃]))
                      && !(column₅ < ARR_SIZE
                      )
                      && row₇ < ARR_SIZE)));
  {
    column := 0;
    while(column < ARR_SIZE)
      decreases ARR_SIZE - column;
      invariant old(column) <= column
        && (forall column₃: int ::
              (  old(column) <= column₃
                && column₃ < column
                 ==> row == column₃
                    && column₃ < ARR_SIZE
                    && array[row][row] == 0
                  ||   row != column₃
                    && column₃ < ARR_SIZE
                    && array[row][column₃] == row))
        && (forall column₃: int ::
              (!(  old(column) <= column₃
                && column₃ < column
              )
                 ==> array[row][row] == old(array)[row][row]
                  && array[row][column₃] == old(array)[row][column₃]));
    {
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
  while(row < ARR_SIZE)
    decreases ARR_SIZE - row;
    invariant old(row) <= row
      && (forall row₁₇: int ::
            (  old(row) <= row₁₇
              && row₁₇ < row
               ==> (exists column₁₄: int ::
                      0 <= column₁₄
                      && (forall column₁₂: int ::
                            (  0 <= column₁₂
                              && column₁₂ < column₁₄
                               ==> column₁₂ < ARR_SIZE))
                      && !(column₁₄ < ARR_SIZE
                      )
                      && row₁₇ < ARR_SIZE)));
  {
    column := 0;
    while(column < ARR_SIZE)
      decreases ARR_SIZE - column;
      invariant old(column) <= column
        && (forall column₁₂: int ::
              (  old(column) <= column₁₂
                && column₁₂ < column
                 ==> column₁₂ < ARR_SIZE));
    {
      sum := sum + array[row][column];
      column := column + 1;
    }
    row := row + 1;
  }
  assert 2 * sum == ARR_SIZE * (ARR_SIZE - 1) * (ARR_SIZE - 1);
  c#result := 0;
  return;
}

