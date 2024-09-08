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
  var c: [int]int;
  var i: int := 0;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> (exists __VERIFIER_nondet_int₁₄: int, __VERIFIER_nondet_int₂₅: int ::
                      i₆ < 100000
                      && a[i₆] == __VERIFIER_nondet_int₁₄
                      && b[i₆] == __VERIFIER_nondet_int₂₅)))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> a[i₆] == old(a)[i₆]
                && b[i₆] == old(b)[i₆]));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    b := b[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < 100000
                && c[i₁₀] == -b[i₁₀] + a[i₁₀]))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> c[i₁₀] == old(c)[i₁₀]));
  {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && x <= 100000
      && (forall x₁₄: int ::
            (  old(x) <= x₁₄
              && x₁₄ < x
               ==> x₁₄ < 100000));
  {
    assert c[x] == a[x] - b[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

