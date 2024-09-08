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
    invariant old(a) <= a
      && a <= 100000
      && (forall a₅: int ::
            (  old(a) <= a₅
              && a₅ < a
               ==> (exists __VERIFIER_nondet_int₁₄: int ::
                      a₅ < 100000
                      && a1[a₅] == __VERIFIER_nondet_int₁₄)))
      && (forall a₅: int ::
            (!(  old(a) <= a₅
              && a₅ < a
            )
               ==> a1[a₅] == old(a1)[a₅]));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < 100000
                && a2[i₉] == a1[i₉]))
      && (forall i₉: int ::
            (!(  old(i) <= i₉
              && i₉ < i
            )
               ==> a2[i₉] == old(a2)[i₉]));
  {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && x <= 100000
      && (forall x₁₃: int ::
            (  old(x) <= x₁₃
              && x₁₃ < x
               ==> x₁₃ < 100000));
  {
    assert a1[x] == a2[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

