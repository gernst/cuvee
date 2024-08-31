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
  var temp: int;
  var index: int;
  var sum: int := 0;
  count := 0;
  while(count < ARR_SIZE)
    decreases ARR_SIZE - count;
    invariant true
      && old(count) <= count
      && count <= ARR_SIZE
      && (forall x₇: int ::
            ((exists count₆: int ::
                    x₇ == count₆
                    && old(count) <= count₆
                    && count₆ < count)
               ==> (exists count₆: int ::
                      count₆ < ARR_SIZE
                      && x₇ == count₆
                      && old(count) <= count₆
                      && count₆ < count
                      && array1[x₇] == 0)))
      && (forall x₇: int ::
            (!((exists count₆: int ::
                    x₇ == count₆
                    && old(count) <= count₆
                    && count₆ < count)
            )
               ==> array1[x₇] == old(array1[x₇])))
      && (forall x₈: int ::
            ((exists count₆: int ::
                    x₈ == count₆
                    && old(count) <= count₆
                    && count₆ < count)
               ==> (exists count₆: int ::
                      count₆ < ARR_SIZE
                      && x₈ == count₆
                      && old(count) <= count₆
                      && count₆ < count
                      && array2[x₈] == 0)))
      && (forall x₈: int ::
            (!((exists count₆: int ::
                    x₈ == count₆
                    && old(count) <= count₆
                    && count₆ < count)
            )
               ==> array2[x₈] == old(array2[x₈])))
      && (forall count₆: int ::
            (  old(count₆) <= count₆
              && old(count) <= count₆
              && count₆ < count
               ==> count₆ < ARR_SIZE));
  {
    array1 := array1[count := 0];
    array2 := array2[count := 0];
    count := count + 1;
  }
  while(1 != 0)
    invariant true
      && (forall x₁₆: int ::
            ((exists index₁₂: int ::
                  x₁₆ == index₁₂)
               ==> (exists index₁₂: int, temp₁₃: int ::
                      temp₁₃ != 0
                      && 0 <= index₁₂
                      && index₁₂ < ARR_SIZE
                      && x₁₆ == index₁₂
                      && array1[x₁₆] == num * num * index₁₂)))
      && (forall x₁₆: int ::
            (!((exists index₁₂: int ::
                  x₁₆ == index₁₂)
            )
               ==> array1[x₁₆] == old(array1[x₁₆])))
      && (forall x₁₇: int ::
            ((exists index₁₂: int ::
                  x₁₇ == -1 + -index₁₂ + ARR_SIZE)
               ==> (exists index₁₂: int, temp₁₃: int ::
                      temp₁₃ != 0
                      && 0 <= index₁₂
                      && index₁₂ < ARR_SIZE
                      && x₁₇ == -1 + -index₁₂ + ARR_SIZE
                      && array2[x₁₇] == num * index₁₂)))
      && (forall x₁₇: int ::
            (!((exists index₁₂: int ::
                  x₁₇ == -1 + -index₁₂ + ARR_SIZE)
            )
               ==> array2[x₁₇] == old(array2[x₁₇])))
      && !((exists index₁₂: int, temp₁₃: int ::
              temp₁₃ == 0
              && 0 <= index₁₂
              && index₁₂ < ARR_SIZE)
      );
  {
    havoc index;
    assume 0 <= index && index < ARR_SIZE;
    array1 := array1[index := num * num * index];
    array2 := array2[ARR_SIZE - 1 - index := num * index];
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
      && (forall count₂₃: int ::
            (  old(count₂₃) <= count₂₃
              && old(count) <= count₂₃
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

