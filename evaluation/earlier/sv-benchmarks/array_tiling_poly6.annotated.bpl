data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var __VERIFIER_nondet_int₁: int;
  var S: int;
  S := __VERIFIER_nondet_int₁;
  assume 1 < S;
  var i: int;
  var a: [int]int;
  i := 0;
  while(i < S)
    decreases S - i;
    invariant old(i) <= i
      && i <= S
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < S
                && a[i₅] == -1 + i₅ * i₅))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]));
  {
    a := a[i := (i - 1) * (i + 1)];
    i := i + 1;
  }
  i := 0;
  while(i < S)
    decreases S - i;
    invariant old(i) <= i
      && i <= S
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ < S
                && a[i₈] == -(i₈ * i₈) + old(a)[i₈]))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> a[i₈] == old(a)[i₈]));
  {
    a := a[i := a[i] - i * i];
    i := i + 1;
  }
  i := 0;
  while(i < S)
    decreases S - i;
    invariant old(i) <= i
      && i <= S
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < S));
  {
    assert a[i] == -1;
    i := i + 1;
  }
  c#result := 0;
  return;
}

