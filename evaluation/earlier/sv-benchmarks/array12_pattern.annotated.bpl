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
                               ==> column₆ < ARR_SIZE
                                && array₇[row₁₀][column₆] == 0))
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
                 ==> column₆ < ARR_SIZE
                  && array[row][column₆] == 0))
        && (forall column₆: int ::
              (!(  old(column) <= column₆
                && column₆ < column
              )
                 ==> array[row][column₆] == old(array)[row][column₆]));
    {
      array[row][column] := 0;
      column := column + 1;
    }
    row := row + 1;
  }
  while(1 != 0)
    invariant (exists index1₁₄: int, index2₁₅: int, temp₁₆: int ::
              temp₁₆ != 0
              && -2147483648 <= temp₁₆
              && temp₁₆ < 2147483648
              && 0 <= index2₁₅
              && index2₁₅ < ARR_SIZE
              && 0 <= index1₁₄
              && index1₁₄ < ARR_SIZE
              && -32768 <= index2₁₅
              && index2₁₅ < 32768
              && -32768 <= index1₁₄
              && index1₁₄ < 32768
              && array[index2₁₅][index1₁₄] == num * num
              && (  index1₁₄ != index2₁₅
                && index2₁₅ != index1₁₄
                 ==> array[index1₁₄][index2₁₅] == num * num * num))
      && !((exists index1₁₄: int, index2₁₅: int, temp₁₆: int ::
              temp₁₆ == 0
              && -2147483648 <= temp₁₆
              && temp₁₆ < 2147483648
              && 0 <= index2₁₅
              && index2₁₅ < ARR_SIZE
              && 0 <= index1₁₄
              && index1₁₄ < ARR_SIZE
              && -32768 <= index2₁₅
              && index2₁₅ < 32768
              && -32768 <= index1₁₄
              && index1₁₄ < 32768)
      );
  {
    havoc index1;
    assume -32768 <= index1 && index1 < 32768;
    havoc index2;
    assume -32768 <= index2 && index2 < 32768;
    assume 0 <= index1 && index1 < ARR_SIZE;
    assume 0 <= index2 && index2 < ARR_SIZE;
    array[index1][index2] := num * num * num;
    array[index2][index1] := num * num;
    havoc temp;
    assume -2147483648 <= temp && temp < 2147483648;
    if(temp == 0) {
      break;
    }
  }
  row := 0;
  while(row < ARR_SIZE)
    decreases ARR_SIZE - row;
    invariant old(row) <= row
      && (forall row₃₀: int ::
            (  old(row) <= row₃₀
              && row₃₀ < row
               ==> (exists column₂₇: int ::
                      0 <= column₂₇
                      && (forall column₂₅: int ::
                            (  0 <= column₂₅
                              && column₂₅ < column₂₇
                               ==> column₂₅ < ARR_SIZE))
                      && !(column₂₇ < ARR_SIZE
                      )
                      && row₃₀ < ARR_SIZE)));
  {
    column := 0;
    while(column < ARR_SIZE)
      decreases ARR_SIZE - column;
      invariant old(column) <= column
        && (forall column₂₅: int ::
              (  old(column) <= column₂₅
                && column₂₅ < column
                 ==> column₂₅ < ARR_SIZE));
    {
      sum := sum + array[row][column];
      column := column + 1;
    }
    row := row + 1;
  }
  assert 0 <= sum && sum <= ARR_SIZE;
  c#result := 0;
  return;
}

