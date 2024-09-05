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
  var max: int := 0;
  var j: int := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant true
      && old(j) <= j
      && j <= 100000
      && (forall x₄: int ::
            ((exists j₃: int ::
                    x₄ == j₃
                    && old(j) <= j₃
                    && j₃ < j)
               ==> (exists __VERIFIER_nondet_int₁₂: int, j₃: int ::
                      j₃ < 100000
                      && x₄ == j₃
                      && old(j) <= j₃
                      && j₃ < j
                      && a[x₄] == __VERIFIER_nondet_int₁₂)))
      && (forall x₄: int ::
            (!((exists j₃: int ::
                    x₄ == j₃
                    && old(j) <= j₃
                    && j₃ < j)
            )
               ==> a[x₄] == old(a[x₄])))
      && (forall j₃: int ::
            (  old(j) <= j₃
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
      && old(i) <= i
      && i <= 100000
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ < 100000));
  {
    if(max < a[i]) {
      max := a[i];
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
    assert a[x] <= max;
    x := x + 1;
  }
  c#result := 0;
  return;
}

