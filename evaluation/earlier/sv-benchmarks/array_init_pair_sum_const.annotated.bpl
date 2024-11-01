data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var N: int := 100000;
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < N
                && a[i₅] == 1
                && b[i₅] == 2))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]
                && b[i₅] == old(b)[i₅]));
  {
    a[i] := 1;
    b[i] := 2;
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < N
                && c[i₉] == b[i₉] + a[i₉]))
      && (forall i₉: int ::
            (!(  old(i) <= i₉
              && i₉ < i
            )
               ==> c[i₉] == old(c)[i₉]));
  {
    c[i] := a[i] + b[i];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < N));
  {
    assert 3 <= c[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

