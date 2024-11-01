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
    invariant (exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₇: int ::
                temp₁₇ != 0
                && -2147483648 <= temp₁₇
                && temp₁₇ < 2147483648
                &&   nondet_short₄₁₄ == nondet_short₅₁₅
                  || nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + ARR_SIZE
                && 0 <= nondet_short₅₁₅
                && nondet_short₅₁₅ < ARR_SIZE
                && 0 <= nondet_short₄₁₄
                && nondet_short₄₁₄ < ARR_SIZE
                && -32768 <= nondet_short₅₁₅
                && nondet_short₅₁₅ < 32768
                && -32768 <= nondet_short₄₁₄
                && nondet_short₄₁₄ < 32768
                && array[nondet_short₄₁₄][nondet_short₅₁₅] == num * num * num * num)
        || (exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₈: int ::
                temp₁₈ != 0
                && -2147483648 <= temp₁₈
                && temp₁₈ < 2147483648
                && !(  nondet_short₄₁₄ == nondet_short₅₁₅
                  || nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + ARR_SIZE
                )
                && 0 <= nondet_short₅₁₅
                && nondet_short₅₁₅ < ARR_SIZE
                && 0 <= nondet_short₄₁₄
                && nondet_short₄₁₄ < ARR_SIZE
                && -32768 <= nondet_short₅₁₅
                && nondet_short₅₁₅ < 32768
                && -32768 <= nondet_short₄₁₄
                && nondet_short₄₁₄ < 32768)
      && !((exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₇: int ::
              temp₁₇ == 0
              && -2147483648 <= temp₁₇
              && temp₁₇ < 2147483648
              &&   nondet_short₄₁₄ == nondet_short₅₁₅
                || nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + ARR_SIZE
              && 0 <= nondet_short₅₁₅
              && nondet_short₅₁₅ < ARR_SIZE
              && 0 <= nondet_short₄₁₄
              && nondet_short₄₁₄ < ARR_SIZE
              && -32768 <= nondet_short₅₁₅
              && nondet_short₅₁₅ < 32768
              && -32768 <= nondet_short₄₁₄
              && nondet_short₄₁₄ < 32768)
      )
      && !((exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₈: int ::
              temp₁₈ == 0
              && -2147483648 <= temp₁₈
              && temp₁₈ < 2147483648
              && !(  nondet_short₄₁₄ == nondet_short₅₁₅
                || nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + ARR_SIZE
              )
              && 0 <= nondet_short₅₁₅
              && nondet_short₅₁₅ < ARR_SIZE
              && 0 <= nondet_short₄₁₄
              && nondet_short₄₁₄ < ARR_SIZE
              && -32768 <= nondet_short₅₁₅
              && nondet_short₅₁₅ < 32768
              && -32768 <= nondet_short₄₁₄
              && nondet_short₄₁₄ < 32768)
      );
  {
    var nondet_short₄: int;
    assume -32768 <= nondet_short₄ && nondet_short₄ < 32768;
    index1 := nondet_short₄;
    var nondet_short₅: int;
    assume -32768 <= nondet_short₅ && nondet_short₅ < 32768;
    index2 := nondet_short₅;
    assume 0 <= index1 && index1 < ARR_SIZE;
    assume 0 <= index2 && index2 < ARR_SIZE;
    var x₆: int;
    if(index1 == index2 || index1 + index2 == ARR_SIZE - 1) {
      x₆ := num * num * num * num;
    } else {
      x₆ := array[index1][index2];
    }
    array[index1][index2] := x₆;
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
  assert sum <= 2 * ARR_SIZE;
  c#result := 0;
  return;
}

