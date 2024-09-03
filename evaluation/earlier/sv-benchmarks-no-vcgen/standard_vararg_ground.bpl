data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var aa: [int]int;
  var a: int := 0;
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && 0 <= i₃
                    && i₃ < i)
               ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                      i₃ < 100000
                      && x₄ == i₃
                      && 0 <= i₃
                      && i₃ < i
                      && aa[x₄] == __VERIFIER_nondet_int₁₂)))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                    x₄ == i₃
                    && 0 <= i₃
                    && i₃ < i)
            )
               ==> aa[x₄] == old(aa[x₄])))
      && (forall i₃: int ::
            (  0 <= i₃
              && i₃ < i
               ==> i₃ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    aa := aa[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  while(0 <= aa[a])
    decreases aa[a] + 1 - 0;
    invariant true
      && 0 <= a
      && 0 <= 1 + aa[a]
      && (forall a₇: int ::
            (  0 <= a₇
              && a₇ < a
               ==> 0 <= aa[a₇]));
  {
    a := a + 1;
  }
  var x: int;
  x := 0;
  while(x < a)
    decreases a - x;
    invariant true
      && 0 <= x
      && x <= a
      && (forall x₁₀: int ::
            (  0 <= x₁₀
              && x₁₀ < x
               ==> x₁₀ < a));
  {
    assert 0 <= aa[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

