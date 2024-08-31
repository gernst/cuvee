data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var ARR_SIZE: int;

procedure main()
  returns (c#result: int)
  modifies ARR_SIZE;
{
  havoc ARR_SIZE;
  assume 0 < ARR_SIZE;
  var array1: [int]int;
  var array2: [int]int;
  var count: int := 0;
  var num: int := -1;
  var sum: int := 0;
  var temp: int;
  var index1: int;
  var index2: int;
  count := 0;
  while(count < ARR_SIZE)
    decreases ARR_SIZE - count;
    invariant true
      && old(count) <= count
      && count <= ARR_SIZE
      && (forall x₈: int ::
            ((exists count₇: int ::
                    x₈ == count₇
                    && old(count) <= count₇
                    && count₇ < count)
               ==> (exists count₇: int ::
                      count₇ < ARR_SIZE
                      && x₈ == count₇
                      && old(count) <= count₇
                      && count₇ < count
                      && array1[x₈] == 0)))
      && (forall x₈: int ::
            (!((exists count₇: int ::
                    x₈ == count₇
                    && old(count) <= count₇
                    && count₇ < count)
            )
               ==> array1[x₈] == old(array1[x₈])))
      && (forall x₉: int ::
            ((exists count₇: int ::
                    x₉ == count₇
                    && old(count) <= count₇
                    && count₇ < count)
               ==> (exists count₇: int ::
                      count₇ < ARR_SIZE
                      && x₉ == count₇
                      && old(count) <= count₇
                      && count₇ < count
                      && array2[x₉] == 0)))
      && (forall x₉: int ::
            (!((exists count₇: int ::
                    x₉ == count₇
                    && old(count) <= count₇
                    && count₇ < count)
            )
               ==> array2[x₉] == old(array2[x₉])))
      && (forall count₇: int ::
            (  old(count₇) <= count₇
              && old(count) <= count₇
              && count₇ < count
               ==> count₇ < ARR_SIZE));
  {
    array1 := array1[count := 0];
    array2 := array2[count := 0];
    count := count + 1;
  }
  count := 1;
  while(1 != 0)
    invariant true
      && (forall x₂₁: int ::
            ((exists index2₁₄: int ::
                  x₂₁ == index2₁₄)
               ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                        temp₁₅ != 0
                        && count₁₈ == 200
                        && array2[index2₁₄] == 0
                        && array1[index1₁₃] == 0
                        && 0 <= index2₁₄
                        && index2₁₄ < ARR_SIZE
                        && 0 <= index1₁₃
                        && index1₁₃ < ARR_SIZE
                        && x₂₁ == index2₁₄
                        && array2[x₂₁] == num * count₁₈)
                || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                        temp₁₆ != 0
                        && count₁₈ != 200
                        && array2[index2₁₄] == 0
                        && array1[index1₁₃] == 0
                        && 0 <= index2₁₄
                        && index2₁₄ < ARR_SIZE
                        && 0 <= index1₁₃
                        && index1₁₃ < ARR_SIZE
                        && x₂₁ == index2₁₄
                        && array2[x₂₁] == num * count₁₈)))
      && (forall x₂₁: int ::
            (!((exists index2₁₄: int ::
                  x₂₁ == index2₁₄)
            )
               ==> array2[x₂₁] == old(array2[x₂₁])))
      && (forall x₂₂: int ::
            ((exists index1₁₃: int ::
                  x₂₂ == index1₁₃)
               ==> (exists index1₁₃: int, index2₁₄: int, temp₁₅: int, count₁₈: int ::
                        temp₁₅ != 0
                        && count₁₈ == 200
                        && array2[index2₁₄] == 0
                        && array1[index1₁₃] == 0
                        && 0 <= index2₁₄
                        && index2₁₄ < ARR_SIZE
                        && 0 <= index1₁₃
                        && index1₁₃ < ARR_SIZE
                        && x₂₂ == index1₁₃
                        && array1[x₂₂] == num * num * count₁₈)
                || (exists index1₁₃: int, index2₁₄: int, temp₁₆: int, count₁₈: int ::
                        temp₁₆ != 0
                        && count₁₈ != 200
                        && array2[index2₁₄] == 0
                        && array1[index1₁₃] == 0
                        && 0 <= index2₁₄
                        && index2₁₄ < ARR_SIZE
                        && 0 <= index1₁₃
                        && index1₁₃ < ARR_SIZE
                        && x₂₂ == index1₁₃
                        && array1[x₂₂] == num * num * count₁₈)))
      && (forall x₂₂: int ::
            (!((exists index1₁₃: int ::
                  x₂₂ == index1₁₃)
            )
               ==> array1[x₂₂] == old(array1[x₂₂])))
      && (forall count₁₈: int ::
              !((exists index1₁₃: int, index2₁₄: int, temp₁₅: int ::
                      temp₁₅ == 0
                      && count₁₈ == 200
                      && array2[index2₁₄] == 0
                      && array1[index1₁₃] == 0
                      && 0 <= index2₁₄
                      && index2₁₄ < ARR_SIZE
                      && 0 <= index1₁₃
                      && index1₁₃ < ARR_SIZE)
              )
              && !((exists index1₁₃: int, index2₁₄: int, temp₁₆: int ::
                      temp₁₆ == 0
                      && count₁₈ != 200
                      && array2[index2₁₄] == 0
                      && array1[index1₁₃] == 0
                      && 0 <= index2₁₄
                      && index2₁₄ < ARR_SIZE
                      && 0 <= index1₁₃
                      && index1₁₃ < ARR_SIZE)
              ));
  {
    havoc index1;
    havoc index2;
    assume 0 <= index1 && index1 < ARR_SIZE;
    assume 0 <= index2 && index2 < ARR_SIZE;
    assume array1[index1] == 0;
    assume array2[index2] == 0;
    array1 := array1[index1 := num * num * count];
    array2 := array2[index2 := num * count];
    if(count == 200) {
      count := 0;
    }
    count := count + 1;
    havoc temp;
    if(temp == 0) {
      break;
    }
  }
  count := 0;
  while(count < ARR_SIZE)
    decreases ARR_SIZE - count;
    invariant true
      && old(count) <= count
      && count <= ARR_SIZE
      && (forall count₃₀: int ::
            (  old(count₃₀) <= count₃₀
              && old(count) <= count₃₀
              && count₃₀ < count
               ==> count₃₀ < ARR_SIZE));
  {
    sum := sum + array1[count] + array2[count];
    count := count + 1;
  }
  assert sum == 0;
  c#result := 0;
  return;
}

