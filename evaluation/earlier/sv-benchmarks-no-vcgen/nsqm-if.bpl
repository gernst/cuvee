data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  havoc N;
  if(N <= 0) {
    c#result := 1;
    return;
  }
  assume N <= 2147483647 / 4;
  var i: int;
  var a: [int]int;
  var b: [int]int;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₆: int ::
            (  x₆ == 0
              && (exists i₅: int ::
                      x₆ == i₅
                      && 0 <= i₅
                      && i₅ < i)
               ==> (exists i₅: int ::
                        i₅ == 0
                        && i₅ < N
                        && x₆ == 0
                        && b[x₆] == 1)
                || (exists i₅: int ::
                        i₅ != 0
                        && i₅ < N
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i
                        && b[x₆] == 2 + old(b)[-1 + i₅])))
      && (forall x₆: int ::
            (!(  x₆ == 0
              && (exists i₅: int ::
                      x₆ == i₅
                      && 0 <= i₅
                      && i₅ < i)
            )
               ==> b[x₆] == old(b[x₆])))
      && (forall i₅: int ::
            (  0 <= i₅
              && i₅ < i
               ==> i₅ < N));
  {
    if(i == 0) {
      b := b[0 := 1];
    } else {
      b := b[i := b[i - 1] + 2];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₁₀: int ::
            (  x₁₀ == 0
              && (exists i₉: int ::
                      x₁₀ == i₉
                      && 0 <= i₉
                      && i₉ < i)
               ==> (exists i₉: int ::
                        i₉ == 0
                        && i₉ < N
                        && x₁₀ == 0
                        && a[x₁₀] == 1 + N)
                || (exists i₉: int ::
                        i₉ != 0
                        && i₉ < N
                        && x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i
                        && a[x₁₀] == 2 + b[-1 + i₉] + old(a)[-1 + i₉])))
      && (forall x₁₀: int ::
            (!(  x₁₀ == 0
              && (exists i₉: int ::
                      x₁₀ == i₉
                      && 0 <= i₉
                      && i₉ < i)
            )
               ==> a[x₁₀] == old(a[x₁₀])))
      && (forall i₉: int ::
            (  0 <= i₉
              && i₉ < i
               ==> i₉ < N));
  {
    if(i == 0) {
      a := a[0 := N + 1];
    } else {
      a := a[i := a[i - 1] + b[i - 1] + 2];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall i₁₃: int ::
            (  0 <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < N));
  {
    assert a[i] == N + (i + 1) * (i + 1);
    i := i + 1;
  }
  c#result := 1;
  return;
}

