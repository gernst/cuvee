data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
               ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                      i₅ < 100000
                      && x₆ == i₅
                      && old(i) <= i₅
                      && i₅ < i
                      && a[x₆] == __VERIFIER_nondet_int₁₄)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists i₉: int ::
                      i₉ < 100000
                      && x₁₀ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && b[x₁₀] == a[99999 + -i₉])))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> b[x₁₀] == old(b[x₁₀])))
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < 100000));
  {
    b := b[i := a[100000 - i - 1]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₁₄: int ::
            (  old(x) <= x₁₄
              && x₁₄ < x
               ==> x₁₄ < 100000));
  {
    assert a[x] == b[100000 - x - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}

