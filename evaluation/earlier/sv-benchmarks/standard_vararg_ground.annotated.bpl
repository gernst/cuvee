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
    invariant old(i) <= i
      && i <= 100000
      && (forall i₃: int ::
            (  old(i) <= i₃
              && i₃ < i
               ==> (exists __VERIFIER_nondet_int₁₂: int ::
                      i₃ < 100000
                      && aa[i₃] == __VERIFIER_nondet_int₁₂)))
      && (forall i₃: int ::
            (!(  old(i) <= i₃
              && i₃ < i
            )
               ==> aa[i₃] == old(aa)[i₃]));
  {
    var __VERIFIER_nondet_int₁: int;
    aa := aa[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  while(0 <= aa[a])
    decreases aa[a] + 1 - 0;
    invariant old(a) <= a
      && 0 <= 1 + aa[a]
      && (forall a₆: int ::
            (  old(a) <= a₆
              && a₆ < a
               ==> 0 <= aa[a₆]));
  {
    a := a + 1;
  }
  var x: int;
  x := 0;
  while(x < a)
    decreases a - x;
    invariant old(x) <= x
      && x <= a
      && (forall x₉: int ::
            (  old(x) <= x₉
              && x₉ < x
               ==> x₉ < a));
  {
    assert 0 <= aa[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

