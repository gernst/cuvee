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
  var min: int := 0;
  var i: int := 0;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
               ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                      i₃ < 100000
                      && x₄ == i₃
                      && old(i) <= i₃
                      && i₃ < i
                      && a[x₄] == __VERIFIER_nondet_int₁₂)))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
            )
               ==> a[x₄] == old(a[x₄])))
      && (forall i₃: int ::
            (  old(i) <= i₃
              && i₃ < i
               ==> i₃ < 100000));
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
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ < 100000));
  {
    if(a[i] < min) {
      min := a[i];
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
      && (forall x₁₂: int ::
            (  old(x) <= x₁₂
              && x₁₂ < x
               ==> x₁₂ < 100000));
  {
    assert min <= a[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

