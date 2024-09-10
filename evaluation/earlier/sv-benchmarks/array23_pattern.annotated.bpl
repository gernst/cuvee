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
  assume -32768 <= nondet_short₁ && nondet_short₁ < 32768;
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
    invariant (exists index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, ARR_SIZE₂₂: int, outerBoundaryPatternCheck₆₂₃: int, temp₂₈: int ::
                temp₂₈ != 0
                && -2147483648 <= temp₂₈
                && temp₂₈ < 2147483648
                && outerBoundaryPatternCheck₆₂₃ != 0
                && outerBoundaryPatternCheck₄₁₈ != 0
                && 0 <= index2₁₅
                && index2₁₅ < ARR_SIZE
                && 0 <= index1₁₄
                && index1₁₄ < ARR_SIZE
                && -32768 <= index2₁₅
                && index2₁₅ < 32768
                && -32768 <= index1₁₄
                && index1₁₄ < 32768
                && array[-1 + -index1₁₄ + ARR_SIZE₂₂][index2₁₅] == num)
        || (exists index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, ARR_SIZE₂₄: int, outerBoundaryPatternCheck₆₂₅: int, temp₂₉: int ::
                temp₂₉ != 0
                && -2147483648 <= temp₂₉
                && temp₂₉ < 2147483648
                && outerBoundaryPatternCheck₆₂₅ != 0
                && outerBoundaryPatternCheck₄₁₈ == 0
                && 0 <= index2₁₅
                && index2₁₅ < ARR_SIZE
                && 0 <= index1₁₄
                && index1₁₄ < ARR_SIZE
                && -32768 <= index2₁₅
                && index2₁₅ < 32768
                && -32768 <= index1₁₄
                && index1₁₄ < 32768
                && array[-1 + -index1₁₄ + ARR_SIZE₂₄][index2₁₅] == num)
        || (exists index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₃: int, temp₃₀: int ::
                temp₃₀ != 0
                && -2147483648 <= temp₃₀
                && temp₃₀ < 2147483648
                && outerBoundaryPatternCheck₆₂₃ == 0
                && outerBoundaryPatternCheck₄₁₈ != 0
                && 0 <= index2₁₅
                && index2₁₅ < ARR_SIZE
                && 0 <= index1₁₄
                && index1₁₄ < ARR_SIZE
                && -32768 <= index2₁₅
                && index2₁₅ < 32768
                && -32768 <= index1₁₄
                && index1₁₄ < 32768
                && array[index1₁₄][index2₁₅] == num * num)
        || (exists index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₅: int, temp₃₁: int ::
                temp₃₁ != 0
                && -2147483648 <= temp₃₁
                && temp₃₁ < 2147483648
                && outerBoundaryPatternCheck₆₂₅ == 0
                && outerBoundaryPatternCheck₄₁₈ == 0
                && 0 <= index2₁₅
                && index2₁₅ < ARR_SIZE
                && 0 <= index1₁₄
                && index1₁₄ < ARR_SIZE
                && -32768 <= index2₁₅
                && index2₁₅ < 32768
                && -32768 <= index1₁₄
                && index1₁₄ < 32768)
      && !((exists index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₃: int, temp₂₈: int ::
              temp₂₈ == 0
              && -2147483648 <= temp₂₈
              && temp₂₈ < 2147483648
              && outerBoundaryPatternCheck₆₂₃ != 0
              && outerBoundaryPatternCheck₄₁₈ != 0
              && 0 <= index2₁₅
              && index2₁₅ < ARR_SIZE
              && 0 <= index1₁₄
              && index1₁₄ < ARR_SIZE
              && -32768 <= index2₁₅
              && index2₁₅ < 32768
              && -32768 <= index1₁₄
              && index1₁₄ < 32768)
      )
      && !((exists index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₅: int, temp₂₉: int ::
              temp₂₉ == 0
              && -2147483648 <= temp₂₉
              && temp₂₉ < 2147483648
              && outerBoundaryPatternCheck₆₂₅ != 0
              && outerBoundaryPatternCheck₄₁₈ == 0
              && 0 <= index2₁₅
              && index2₁₅ < ARR_SIZE
              && 0 <= index1₁₄
              && index1₁₄ < ARR_SIZE
              && -32768 <= index2₁₅
              && index2₁₅ < 32768
              && -32768 <= index1₁₄
              && index1₁₄ < 32768)
      )
      && !((exists index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₃: int, temp₃₀: int ::
              temp₃₀ == 0
              && -2147483648 <= temp₃₀
              && temp₃₀ < 2147483648
              && outerBoundaryPatternCheck₆₂₃ == 0
              && outerBoundaryPatternCheck₄₁₈ != 0
              && 0 <= index2₁₅
              && index2₁₅ < ARR_SIZE
              && 0 <= index1₁₄
              && index1₁₄ < ARR_SIZE
              && -32768 <= index2₁₅
              && index2₁₅ < 32768
              && -32768 <= index1₁₄
              && index1₁₄ < 32768)
      )
      && !((exists index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₅: int, temp₃₁: int ::
              temp₃₁ == 0
              && -2147483648 <= temp₃₁
              && temp₃₁ < 2147483648
              && outerBoundaryPatternCheck₆₂₅ == 0
              && outerBoundaryPatternCheck₄₁₈ == 0
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
    var outerBoundaryPatternCheck₄: int;
    outerBoundaryPatternCheck₄ := call outerBoundaryPatternCheck(index1);
    var x₅: int;
    if(outerBoundaryPatternCheck₄ != 0) {
      x₅ := num * num;
    } else {
      x₅ := array[index1][index2];
    }
    array[index1][index2] := x₅;
    var outerBoundaryPatternCheck₆: int;
    outerBoundaryPatternCheck₆ := call outerBoundaryPatternCheck(index1);
    var x₇: int;
    if(outerBoundaryPatternCheck₆ != 0) {
      x₇ := num;
    } else {
      x₇ := array[ARR_SIZE - 1 - index1][index2];
    }
    array[((ARR_SIZE - 1) - index1)][index2] := x₇;
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
      && (forall row₄₅: int ::
            (  old(row) <= row₄₅
              && row₄₅ < row
               ==> (exists column₄₂: int ::
                      0 <= column₄₂
                      && (forall column₄₀: int ::
                            (  0 <= column₄₀
                              && column₄₀ < column₄₂
                               ==> column₄₀ < ARR_SIZE))
                      && !(column₄₂ < ARR_SIZE
                      )
                      && row₄₅ < ARR_SIZE)));
  {
    column := 0;
    while(column < ARR_SIZE)
      decreases ARR_SIZE - column;
      invariant old(column) <= column
        && (forall column₄₀: int ::
              (  old(column) <= column₄₀
                && column₄₀ < column
                 ==> column₄₀ < ARR_SIZE));
    {
      sum := sum + array[row][column];
      column := column + 1;
    }
    row := row + 1;
  }
  assert sum == 0;
  c#result := 0;
  return;
}

