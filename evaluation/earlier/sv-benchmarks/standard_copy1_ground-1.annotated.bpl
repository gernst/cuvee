data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a1: [int]int;
  var a2: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && old(a) <= a
      && a <= 100000
      && (forall x₆: int ::
            ((exists a₅: int ::
                    x₆ == a₅
                    && old(a) <= a₅
                    && a₅ < a)
               ==> (exists __VERIFIER_nondet_int₁₄: int, a₅: int ::
                      a₅ < 100000
                      && x₆ == a₅
                      && old(a) <= a₅
                      && a₅ < a
                      && a1[x₆] == __VERIFIER_nondet_int₁₄)))
      && (forall x₆: int ::
            (!((exists a₅: int ::
                    x₆ == a₅
                    && old(a) <= a₅
                    && a₅ < a)
            )
               ==> a1[x₆] == old(a1[x₆])))
      && (forall a₅: int ::
            (  old(a) <= a₅
              && a₅ < a
               ==> a₅ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₁: int ::
            ((exists i₁₀: int ::
                    x₁₁ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
               ==> (exists i₁₀: int ::
                      i₁₀ < 100000
                      && x₁₁ == i₁₀
                      && old(i) <= i₁₀
                      && i₁₀ < i
                      && a2[x₁₁] == a1[i₁₀])))
      && (forall x₁₁: int ::
            (!((exists i₁₀: int ::
                    x₁₁ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
            )
               ==> a2[x₁₁] == old(a2[x₁₁])))
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < 100000));
  {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₁₅: int ::
            (  old(x) <= x₁₅
              && x₁₅ < x
               ==> x₁₅ < 100000));
  {
    assert a1[x] == a2[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

