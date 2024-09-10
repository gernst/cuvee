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
  var pivot: int;
  count := 0;
  while(count < ARR_SIZE)
    decreases ARR_SIZE - count;
    invariant old(count) <= count
      && (forall count₇: int ::
            (  old(count) <= count₇
              && count₇ < count
               ==> count₇ < ARR_SIZE
                && array1[count₇] == num * num * count₇
                && array2[count₇] == num * count₇))
      && (forall count₇: int ::
            (!(  old(count) <= count₇
              && count₇ < count
            )
               ==> array1[count₇] == old(array1)[count₇]
                && array2[count₇] == old(array2)[count₇]));
  {
    array1[count] := num * num * count;
    array2[count] := num * count;
    count := count + 1;
  }
  while(1 != 0)
    invariant (exists nondet_short₃₁₁: int, nondet_short₄₁₂: int, temp₁₃: int ::
              temp₁₃ != 0
              && -2147483648 <= temp₁₃
              && temp₁₃ < 2147483648
              && nondet_short₄₁₂ <= nondet_short₃₁₁
              && nondet_short₃₁₁ < -nondet_short₄₁₂ + ARR_SIZE
              && 0 < nondet_short₄₁₂
              && -32768 <= nondet_short₄₁₂
              && nondet_short₄₁₂ < 32768
              && -32768 <= nondet_short₃₁₁
              && nondet_short₃₁₁ < 32768
              && array2[nondet_short₃₁₁] == old(array2)[nondet_short₃₁₁ + nondet_short₄₁₂] + old(array2)[nondet_short₃₁₁ + -nondet_short₄₁₂]
              && array1[nondet_short₃₁₁] == old(array1)[nondet_short₃₁₁ + -nondet_short₄₁₂] + old(array1)[nondet_short₃₁₁ + nondet_short₄₁₂])
      && !((exists nondet_short₃₁₁: int, nondet_short₄₁₂: int, temp₁₃: int ::
              temp₁₃ == 0
              && -2147483648 <= temp₁₃
              && temp₁₃ < 2147483648
              && nondet_short₄₁₂ <= nondet_short₃₁₁
              && nondet_short₃₁₁ < -nondet_short₄₁₂ + ARR_SIZE
              && 0 < nondet_short₄₁₂
              && -32768 <= nondet_short₄₁₂
              && nondet_short₄₁₂ < 32768
              && -32768 <= nondet_short₃₁₁
              && nondet_short₃₁₁ < 32768)
      );
  {
    var nondet_short₃: int;
    assume -32768 <= nondet_short₃ && nondet_short₃ < 32768;
    index := nondet_short₃;
    var nondet_short₄: int;
    assume -32768 <= nondet_short₄ && nondet_short₄ < 32768;
    pivot := nondet_short₄;
    assume 0 < pivot;
    assume pivot <= index && index < ARR_SIZE - pivot;
    array1[index] := array1[index - pivot] + array1[index + pivot];
    array2[index] := array2[index - pivot] + array2[index + pivot];
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
      && (forall count₂₃: int ::
            (  old(count) <= count₂₃
              && count₂₃ < count
               ==> count₂₃ < ARR_SIZE));
  {
    sum := sum + array1[count] + array2[count];
    count := count + 1;
  }
  assert sum == 0;
  c#result := 0;
  return;
}

