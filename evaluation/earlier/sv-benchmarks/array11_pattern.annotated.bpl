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
  var array1: [int]int;
  var array2: [int]int;
  var count: int := 0;
  var num: int := -1;
  var sum: int := 0;
  var temp: int;
  var index: int;
  count := 0;
  while(count < ARR_SIZE)
    decreases ARR_SIZE - count;
    invariant old(count) <= count
      && (forall count₆: int ::
            (  old(count) <= count₆
              && count₆ < count
               ==> count₆ < ARR_SIZE
                && array1[count₆] == 0
                && array2[count₆] == 0))
      && (forall count₆: int ::
            (!(  old(count) <= count₆
              && count₆ < count
            )
               ==> array1[count₆] == old(array1)[count₆]
                && array2[count₆] == old(array2)[count₆]));
  {
    array1[count] := 0;
    array2[count] := 0;
    count := count + 1;
  }
  while(1 != 0)
    invariant (exists nondet_short₃₁₀: int, temp₁₂: int ::
                temp₁₂ != 0
                && -2147483648 <= temp₁₂
                && temp₁₂ < 2147483648
                && nondet_short₃₁₀ == -1 + ARR_SIZE
                && 0 <= nondet_short₃₁₀
                && nondet_short₃₁₀ < ARR_SIZE
                && -32768 <= nondet_short₃₁₀
                && nondet_short₃₁₀ < 32768
                && array1[nondet_short₃₁₀] == num * num * num * num * nondet_short₃₁₀
                && array2[nondet_short₃₁₀] == nondet_short₃₁₀)
        || (exists nondet_short₃₁₀: int, temp₁₃: int ::
                temp₁₃ != 0
                && -2147483648 <= temp₁₃
                && temp₁₃ < 2147483648
                && nondet_short₃₁₀ != -1 + ARR_SIZE
                && 0 <= nondet_short₃₁₀
                && nondet_short₃₁₀ < ARR_SIZE
                && -32768 <= nondet_short₃₁₀
                && nondet_short₃₁₀ < 32768
                && array1[nondet_short₃₁₀] == num * num * num * num * nondet_short₃₁₀
                && array2[nondet_short₃₁₀] == num * nondet_short₃₁₀)
      && !((exists nondet_short₃₁₀: int, temp₁₂: int ::
              temp₁₂ == 0
              && -2147483648 <= temp₁₂
              && temp₁₂ < 2147483648
              && nondet_short₃₁₀ == -1 + ARR_SIZE
              && 0 <= nondet_short₃₁₀
              && nondet_short₃₁₀ < ARR_SIZE
              && -32768 <= nondet_short₃₁₀
              && nondet_short₃₁₀ < 32768)
      )
      && !((exists nondet_short₃₁₀: int, temp₁₃: int ::
              temp₁₃ == 0
              && -2147483648 <= temp₁₃
              && temp₁₃ < 2147483648
              && nondet_short₃₁₀ != -1 + ARR_SIZE
              && 0 <= nondet_short₃₁₀
              && nondet_short₃₁₀ < ARR_SIZE
              && -32768 <= nondet_short₃₁₀
              && nondet_short₃₁₀ < 32768)
      );
  {
    var nondet_short₃: int;
    assume -32768 <= nondet_short₃ && nondet_short₃ < 32768;
    index := nondet_short₃;
    assume 0 <= index && index < ARR_SIZE;
    array1[index] := num * num * num * num * index;
    var x₄: int;
    if(index == ARR_SIZE - 1) {
      x₄ := index;
    } else {
      x₄ := num * index;
    }
    array2[index] := x₄;
    havoc temp;
    assume -2147483648 <= temp && temp < 2147483648;
    if(temp == 0) {
      break;
    }
  }
  count := 0;
  while(count < ARR_SIZE)
    decreases ARR_SIZE - count;
    invariant old(count) <= count
      && (forall count₂₁: int ::
            (  old(count) <= count₂₁
              && count₂₁ < count
               ==> count₂₁ < ARR_SIZE));
  {
    sum := sum + array1[count] + array2[count];
    count := count + 1;
  }
  assert sum == 0 || sum + 2 == 2 * ARR_SIZE;
  c#result := 0;
  return;
}

