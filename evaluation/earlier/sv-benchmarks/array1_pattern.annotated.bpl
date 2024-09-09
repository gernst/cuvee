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
    array1 := array1[count := 0];
    array2 := array2[count := 0];
    count := count + 1;
  }
  while(1 != 0)
    invariant (exists index₁₀: int, temp₁₁: int ::
              temp₁₁ != 0
              && 0 <= index₁₀
              && index₁₀ < ARR_SIZE
              && array1[index₁₀] == num * num * index₁₀
              && array2[-1 + -index₁₀ + ARR_SIZE] == num * index₁₀)
      && !((exists index₁₀: int, temp₁₁: int ::
              temp₁₁ == 0
              && 0 <= index₁₀
              && index₁₀ < ARR_SIZE)
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
    invariant old(count) <= count
      && (forall count₁₉: int ::
            (  old(count) <= count₁₉
              && count₁₉ < count
               ==> count₁₉ < ARR_SIZE));
  {
    sum := sum + array1[count] + array2[count];
    count := count + 1;
  }
  assert sum == 0;
  c#result := 0;
  return;
}

