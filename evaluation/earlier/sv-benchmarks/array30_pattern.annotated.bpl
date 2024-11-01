data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var ARR_SIZE: int;

procedure diff(idx1: int, idx2: int)
  returns (c#result: int)
  modifies ARR_SIZE;
{
  if(idx2 < idx1) {
    c#result := idx1 - idx2;
    return;
  } else {
    c#result := idx2 - idx1;
    return;
  }
}

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
      && (forall row₁₀: int ::
            (  old(row) <= row₁₀
              && row₁₀ < row
               ==> (exists array₇: [int][int]int, column₈: int ::
                      0 <= column₈
                      && (forall column₆: int ::
                            (  0 <= column₆
                              && column₆ < column₈
                               ==> (exists diff₂₅: int ::
                                      column₆ < ARR_SIZE
                                      && array₇[row₁₀][column₆] == diff₂₅)))
                      && (forall column₆: int ::
                            (!(  0 <= column₆
                              && column₆ < column₈
                            )
                               ==> array₇[row₁₀][column₆] == array[row₁₀][column₆]))
                      && !(column₈ < ARR_SIZE
                      )
                      && row₁₀ < ARR_SIZE)));
  {
    column := 0;
    while(column < ARR_SIZE)
      decreases ARR_SIZE - column;
      invariant old(column) <= column
        && (forall column₆: int ::
              (  old(column) <= column₆
                && column₆ < column
                 ==> (exists diff₂₅: int ::
                        column₆ < ARR_SIZE
                        && array[row][column₆] == diff₂₅)))
        && (forall column₆: int ::
              (!(  old(column) <= column₆
                && column₆ < column
              )
                 ==> array[row][column₆] == old(array)[row][column₆]));
    {
      var diff₂: int;
      diff₂ := call diff(row, column);
      array[row][column] := diff₂;
      column := column + 1;
    }
    row := row + 1;
  }
  row := 0;
  while(row < ARR_SIZE)
    decreases ARR_SIZE - row;
    invariant old(row) <= row
      && (forall row₂₀: int ::
            (  old(row) <= row₂₀
              && row₂₀ < row
               ==> (exists column₁₇: int ::
                      0 <= column₁₇
                      && (forall column₁₅: int ::
                            (  0 <= column₁₅
                              && column₁₅ < column₁₇
                               ==> column₁₅ < ARR_SIZE))
                      && !(column₁₇ < ARR_SIZE
                      )
                      && row₂₀ < ARR_SIZE)));
  {
    column := 0;
    while(column < ARR_SIZE)
      decreases ARR_SIZE - column;
      invariant old(column) <= column
        && (forall column₁₅: int ::
              (  old(column) <= column₁₅
                && column₁₅ < column
                 ==> column₁₅ < ARR_SIZE));
    {
      sum := sum + array[row][column];
      column := column + 1;
    }
    row := row + 1;
  }
  assert 3 * sum == ARR_SIZE * (ARR_SIZE - 1) * (ARR_SIZE + 1);
  c#result := 0;
  return;
}

