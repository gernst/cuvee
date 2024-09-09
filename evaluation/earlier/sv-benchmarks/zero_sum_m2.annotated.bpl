data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var SIZE: int;

procedure main()
  returns (c#result: int)
  modifies SIZE;
{
  havoc SIZE;
  if(1 < SIZE) {
    var i: int;
    var a: [int]int;
    var sum: int := 0;
    {
      var i: int := 0;
      while(i < SIZE)
        decreases SIZE - i;
        invariant old(i) <= i
          && (forall i₅: int ::
                (  old(i) <= i₅
                  && i₅ < i
                   ==> (exists __VERIFIER_nondet_short₁₄: int ::
                          i₅ < SIZE
                          && a[i₅] == __VERIFIER_nondet_short₁₄)))
          && (forall i₅: int ::
                (!(  old(i) <= i₅
                  && i₅ < i
                )
                   ==> a[i₅] == old(a)[i₅]));
      {
        var __VERIFIER_nondet_short₁: int;
        a := a[i := __VERIFIER_nondet_short₁];
        i := i + 1;
      }
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₉: int ::
              (  old(i) <= i₉
                && i₉ < i
                 ==> i₉ < SIZE));
    {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₁₃: int ::
              (  old(i) <= i₁₃
                && i₁₃ < i
                 ==> i₁₃ < SIZE));
    {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₁₇: int ::
              (  old(i) <= i₁₇
                && i₁₇ < i
                 ==> i₁₇ < SIZE));
    {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₂₁: int ::
              (  old(i) <= i₂₁
                && i₂₁ < i
                 ==> i₂₁ < SIZE));
    {
      sum := sum - a[i];
      i := i + 1;
    }
    assert sum == 0;
  }
  c#result := 1;
  return;
}

