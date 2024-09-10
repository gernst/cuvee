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
    invariant (exists index1₁₄: int, index2₁₅: int, temp₁₇: int ::
                temp₁₇ != 0
                && -2147483648 <= temp₁₇
                && temp₁₇ < 2147483648
                &&   index2₁₅ + index1₁₄ == -2 + ARR_SIZE
                  || index2₁₅ + index1₁₄ == ARR_SIZE
                && 0 <= index2₁₅
                && index2₁₅ < ARR_SIZE
                && 0 <= index1₁₄
                && index1₁₄ < ARR_SIZE
                && -32768 <= index2₁₅
                && index2₁₅ < 32768
                && -32768 <= index1₁₄
                && index1₁₄ < 32768
                && array[index1₁₄][index2₁₅] == num * num * num * num)
        || (exists index1₁₄: int, index2₁₅: int, temp₁₈: int ::
                temp₁₈ != 0
                && -2147483648 <= temp₁₈
                && temp₁₈ < 2147483648
                && !(  index2₁₅ + index1₁₄ == -2 + ARR_SIZE
                  || index2₁₅ + index1₁₄ == ARR_SIZE
                )
                && 0 <= index2₁₅
                && index2₁₅ < ARR_SIZE
                && 0 <= index1₁₄
                && index1₁₄ < ARR_SIZE
                && -32768 <= index2₁₅
                && index2₁₅ < 32768
                && -32768 <= index1₁₄
                && index1₁₄ < 32768)
      && !((exists index1₁₄: int, index2₁₅: int, temp₁₇: int ::
              temp₁₇ == 0
              && -2147483648 <= temp₁₇
              && temp₁₇ < 2147483648
              &&   index2₁₅ + index1₁₄ == -2 + ARR_SIZE
                || index2₁₅ + index1₁₄ == ARR_SIZE
              && 0 <= index2₁₅
              && index2₁₅ < ARR_SIZE
              && 0 <= index1₁₄
              && index1₁₄ < ARR_SIZE
              && -32768 <= index2₁₅
              && index2₁₅ < 32768
              && -32768 <= index1₁₄
              && index1₁₄ < 32768)
      )
      && !((exists index1₁₄: int, index2₁₅: int, temp₁₈: int ::
              temp₁₈ == 0
              && -2147483648 <= temp₁₈
              && temp₁₈ < 2147483648
              && !(  index2₁₅ + index1₁₄ == -2 + ARR_SIZE
                || index2₁₅ + index1₁₄ == ARR_SIZE
              )
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
    temp := index1 + index2;
    var x₄: int;
    if(temp == ARR_SIZE - 2 || temp == ARR_SIZE) {
      x₄ := num * num * num * num;
    } else {
      x₄ := array[index1][index2];
    }
    array[index1][index2] := x₄;
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
      && (forall row₃₂: int ::
            (  old(row) <= row₃₂
              && row₃₂ < row
               ==> (exists column₂₉: int ::
                      0 <= column₂₉
                      && (forall column₂₇: int ::
                            (  0 <= column₂₇
                              && column₂₇ < column₂₉
                               ==> column₂₇ < ARR_SIZE))
                      && !(column₂₉ < ARR_SIZE
                      )
                      && row₃₂ < ARR_SIZE)));
  {
    column := 0;
    while(column < ARR_SIZE)
      decreases ARR_SIZE - column;
      invariant old(column) <= column
        && (forall column₂₇: int ::
              (  old(column) <= column₂₇
                && column₂₇ < column
                 ==> column₂₇ < ARR_SIZE));
    {
      sum := sum + array[row][column];
      column := column + 1;
    }
    row := row + 1;
  }
  assert sum <= 2 * (ARR_SIZE - 1);
  c#result := 0;
  return;
}

