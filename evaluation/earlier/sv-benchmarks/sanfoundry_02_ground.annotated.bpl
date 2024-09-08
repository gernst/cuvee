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
    invariant old(i) <= i
      && i <= 100000
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> (exists __VERIFIER_nondet_int₁₆: int ::
                      i₇ < 100000
                      && array[i₇] == __VERIFIER_nondet_int₁₆)))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> array[i₇] == old(array)[i₇]));
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
    invariant old(i) <= i
      && i <= 100000
      && (forall largest2₁₀: int, largest1₁₁: int, i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> largest1₁₁ <= array[i₁₂]
                  && i₁₂ < 100000
                ||   largest2₁₀ < array[i₁₂]
                  && !(largest1₁₁ <= array[i₁₂]
                  )
                  && i₁₂ < 100000
                ||   !(largest2₁₀ < array[i₁₂]
                  )
                  && !(largest1₁₁ <= array[i₁₂]
                  )
                  && i₁₂ < 100000));
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
    invariant old(x) <= x
      && x <= 100000
      && (forall x₂₁: int ::
            (  old(x) <= x₂₁
              && x₂₁ < x
               ==> x₂₁ < 100000));
  {
    assert array[x] <= largest1;
    x := x + 1;
  }
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && x <= 100000
      && (forall x₂₄: int ::
            (  old(x) <= x₂₄
              && x₂₄ < x
               ==> x₂₄ < 100000));
  {
    assert array[x] <= largest2 || array[x] == largest1;
    x := x + 1;
  }
  c#result := 0;
  return;
}

