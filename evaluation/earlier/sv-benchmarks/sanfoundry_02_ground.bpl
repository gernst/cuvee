data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var array: [int]int;
  var i: int;
  var largest1: int;
  var largest2: int;
  var temp: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₈: int ::
            ((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₁₆: int, i₇: int ::
                      i₇ < 100000
                      && x₈ == i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && array[x₈] == __VERIFIER_nondet_int₁₆)))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> array[x₈] == old(array[x₈])))
      && (forall i₇: int ::
            (  old(i₇) <= i₇
              && old(i) <= i₇
              && i₇ < i
               ==> i₇ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    array := array[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  largest1 := array[0];
  largest2 := array[1];
  if(largest1 < largest2) {
    temp := largest1;
    largest1 := largest2;
    largest2 := temp;
  }
  i := 2;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall i₁₃: int ::
            (  old(i₁₃) <= i₁₃
              && old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 100000));
  {
    if(largest1 <= array[i]) {
      largest2 := largest1;
      largest1 := array[i];
    } else {
      if(largest2 < array[i]) {
        largest2 := array[i];
      }
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₂₂: int ::
            (  old(x₂₂) <= x₂₂
              && old(x) <= x₂₂
              && x₂₂ < x
               ==> x₂₂ < 100000));
  {
    assert array[x] <= largest1;
    x := x + 1;
  }
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₂₅: int ::
            (  old(x₂₅) <= x₂₅
              && old(x) <= x₂₅
              && x₂₅ < x
               ==> x₂₅ < 100000));
  {
    assert array[x] <= largest2 || array[x] == largest1;
    x := x + 1;
  }
  c#result := 0;
  return;
}

