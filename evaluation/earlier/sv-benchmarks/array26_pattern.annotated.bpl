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
  assume 1 < ARR_SIZE;
  var array: [int][int]int;
  var row: int := 0;
  var column: int := 0;
  var num: int := -1;
  var value: int := 1;
  var sum: int := 0;
  row := 0;
  while(row < ARR_SIZE)
    decreases ARR_SIZE - row;
    invariant old(row) <= row
      && (forall row₁₀: int ::
            (  old(row) <= row₁₀
              && row₁₀ < row
               ==> (exists array₅: [int][int]int, column₇: int ::
                      0 <= column₇
                      && (forall value₃: int, column₄: int ::
                            (  0 <= column₄
                              && column₄ < column₇
                               ==> row₁₀ % 2 == 0
                                  && column₄ % 2 == 0
                                  && column₄ < ARR_SIZE
                                  && array₅[row₁₀][column₄] == value₃
                                ||   row₁₀ % 2 == 1
                                  && column₄ % 2 == 1
                                  && !(  row₁₀ % 2 == 0
                                    && column₄ % 2 == 0
                                  )
                                  && column₄ < ARR_SIZE
                                  && array₅[row₁₀][column₄] == value₃
                                ||   !(  row₁₀ % 2 == 1
                                    && column₄ % 2 == 1
                                  )
                                  && !(  row₁₀ % 2 == 0
                                    && column₄ % 2 == 0
                                  )
                                  && column₄ < ARR_SIZE
                                  && array₅[row₁₀][column₄] == 0))
                      && (forall column₄: int ::
                            (!(  0 <= column₄
                              && column₄ < column₇
                            )
                               ==> array₅[row₁₀][column₄] == array[row₁₀][column₄]))
                      && !(column₇ < ARR_SIZE
                      )
                      && row₁₀ < ARR_SIZE)));
  {
    column := 0;
    while(column < ARR_SIZE)
      decreases ARR_SIZE - column;
      invariant old(column) <= column
        && (forall value₃: int, column₄: int ::
              (  old(column) <= column₄
                && column₄ < column
                 ==> row % 2 == 0
                    && column₄ % 2 == 0
                    && column₄ < ARR_SIZE
                    && array[row][column₄] == value₃
                  ||   row % 2 == 1
                    && column₄ % 2 == 1
                    && !(  row % 2 == 0
                      && column₄ % 2 == 0
                    )
                    && column₄ < ARR_SIZE
                    && array[row][column₄] == value₃
                  ||   !(  row % 2 == 1
                      && column₄ % 2 == 1
                    )
                    && !(  row % 2 == 0
                      && column₄ % 2 == 0
                    )
                    && column₄ < ARR_SIZE
                    && array[row][column₄] == 0))
        && (forall column₄: int ::
              (!(  old(column) <= column₄
                && column₄ < column
              )
                 ==> array[row][column₄] == old(array)[row][column₄]));
    {
      if(row % 2 == 0 && column % 2 == 0) {
        array[row][column] := value;
        value := value * num;
      } else {
        if(row % 2 == 1 && column % 2 == 1) {
          array[row][column] := value;
          value := value * num;
        } else {
          array[row][column] := 0;
        }
      }
      column := column + 1;
    }
    row := row + 1;
  }
  row := 0;
  while(row < ARR_SIZE)
    decreases ARR_SIZE - row;
    invariant old(row) <= row
      && (forall row₂₁: int ::
            (  old(row) <= row₂₁
              && row₂₁ < row
               ==> (exists column₁₈: int ::
                      0 <= column₁₈
                      && (forall column₁₆: int ::
                            (  0 <= column₁₆
                              && column₁₆ < column₁₈
                               ==> column₁₆ < ARR_SIZE))
                      && !(column₁₈ < ARR_SIZE
                      )
                      && row₂₁ < ARR_SIZE)));
  {
    column := 0;
    while(column < ARR_SIZE)
      decreases ARR_SIZE - column;
      invariant old(column) <= column
        && (forall column₁₆: int ::
              (  old(column) <= column₁₆
                && column₁₆ < column
                 ==> column₁₆ < ARR_SIZE));
    {
      sum := sum + array[row][column];
      column := column + 1;
    }
    row := row + 1;
  }
  assert sum == 0 || sum == 1;
  c#result := 0;
  return;
}

