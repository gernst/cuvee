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
    invariant true
      && old(i) <= i
      && i <= S
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
               ==> (exists i₅: int ::
                      i₅ < S
                      && x₆ == i₅
                      && old(i) <= i₅
                      && i₅ < i
                      && a[x₆] == -1 + i₅ * i₅)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < S));
  {
    a := a[i := (i - 1) * (i + 1)];
    i := i + 1;
  }
  i := 0;
  while(i < S)
    decreases S - i;
    invariant true
      && old(i) <= i
      && i <= S
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists i₉: int ::
                      i₉ < S
                      && x₁₀ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && a[x₁₀] == old(a)[i₉] + -(i₉ * i₉))))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> a[x₁₀] == old(a[x₁₀])))
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < S));
  {
    a := a[i := a[i] - i * i];
    i := i + 1;
  }
  i := 0;
  while(i < S)
    decreases S - i;
    invariant true
      && old(i) <= i
      && i <= S
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < S));
  {
    assert a[i] == -1;
    i := i + 1;
  }
  c#result := 0;
  return;
}

