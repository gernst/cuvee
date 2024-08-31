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
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₅: int ::
            ((exists i₄: int ::
                    x₅ == i₄
                    && old(i) <= i₄
                    && i₄ < i)
               ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                      i₄ < 100000
                      && x₅ == i₄
                      && old(i) <= i₄
                      && i₄ < i
                      && array[x₅] == __VERIFIER_nondet_int₁₃)))
      && (forall x₅: int ::
            (!((exists i₄: int ::
                    x₅ == i₄
                    && old(i) <= i₄
                    && i₄ < i)
            )
               ==> array[x₅] == old(array[x₅])))
      && (forall i₄: int ::
            (  old(i₄) <= i₄
              && old(i) <= i₄
              && i₄ < i
               ==> i₄ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    array := array[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  var largest: int := array[0];
  i := 1;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall i₉: int ::
            (  old(i₉) <= i₉
              && old(i) <= i₉
              && i₉ < i
               ==> i₉ < 100000));
  {
    if(largest < array[i]) {
      largest := array[i];
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
      && (forall x₁₃: int ::
            (  old(x₁₃) <= x₁₃
              && old(x) <= x₁₃
              && x₁₃ < x
               ==> x₁₃ < 100000));
  {
    assert array[x] <= largest;
    x := x + 1;
  }
  c#result := 0;
  return;
}

