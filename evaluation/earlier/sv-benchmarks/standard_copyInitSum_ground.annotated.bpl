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
    invariant old(i) <= i
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < 100000
                && a[i₅] == 42))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]));
  {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ < 100000
                && b[i₈] == a[i₈]))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> b[i₈] == old(b)[i₈]));
  {
    b := b[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < 100000
                && b[i₁₁] == old(b)[i₁₁] + incr))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> b[i₁₁] == old(b)[i₁₁]));
  {
    b := b[i := b[i] + incr];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₁₅: int ::
            (  old(x) <= x₁₅
              && x₁₅ < x
               ==> x₁₅ < 100000));
  {
    assert b[x] == 42 + incr;
    x := x + 1;
  }
  c#result := 0;
  return;
}

