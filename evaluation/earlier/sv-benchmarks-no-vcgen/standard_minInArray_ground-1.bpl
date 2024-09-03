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
  var j: int := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant true
      && 0 <= j
      && j <= 100000
      && (forall x₄: int ::
            ((exists j₃: int ::
                    x₄ == j₃
                    && 0 <= j₃
                    && j₃ < j)
               ==> (exists __VERIFIER_nondet_int₁₂: int, j₃: int ::
                      j₃ < 100000
                      && x₄ == j₃
                      && 0 <= j₃
                      && j₃ < j
                      && a[x₄] == __VERIFIER_nondet_int₁₂)))
      && (forall x₄: int ::
            (!((exists j₃: int ::
                    x₄ == j₃
                    && 0 <= j₃
                    && j₃ < j)
            )
               ==> a[x₄] == old(a[x₄])))
      && (forall j₃: int ::
            (  0 <= j₃
              && j₃ < j
               ==> j₃ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[j := __VERIFIER_nondet_int₁];
    j := j + 1;
  }
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall i₈: int ::
            (  0 <= i₈
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
      && 0 <= x
      && x <= 100000
      && (forall x₁₂: int ::
            (  0 <= x₁₂
              && x₁₂ < x
               ==> x₁₂ < 100000));
  {
    assert min < a[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

