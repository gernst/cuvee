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
  var __VERIFIER_nondet_int₁: int;
  var incr: int;
  incr := __VERIFIER_nondet_int₁;
  var i: int := 0;
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
               ==> (exists i₅: int ::
                      i₅ < 100000
                      && x₆ == i₅
                      && old(i) <= i₅
                      && i₅ < i
                      && a[x₆] == 42)))
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
    a := a[i := 42];
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
                      && b[x₁₀] == a[i₉])))
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
    b := b[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
               ==> (exists i₁₃: int ::
                      i₁₃ < 100000
                      && x₁₄ == i₁₃
                      && old(i) <= i₁₃
                      && i₁₃ < i
                      && b[x₁₄] == incr + old(b)[i₁₃])))
      && (forall x₁₄: int ::
            (!((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
            )
               ==> b[x₁₄] == old(b[x₁₄])))
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 100000));
  {
    b := b[i := b[i] + incr];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₁₈: int ::
            (  old(x) <= x₁₈
              && x₁₈ < x
               ==> x₁₈ < 100000));
  {
    assert b[x] == 42 + incr;
    x := x + 1;
  }
  c#result := 0;
  return;
}

