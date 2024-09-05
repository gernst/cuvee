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
  var sum: [int]int;
  var a: [int]int;
  sum := sum[0 := 0];
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₆: int ::
            (x₆ == 0
               ==> (exists i₅: int ::
                      i₅ < N
                      && x₆ == 0
                      && sum[x₆] == 1 + old(sum)[0])))
      && (forall x₆: int ::
            (x₆ != 0
               ==> sum[x₆] == old(sum[x₆])))
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < N));
  {
    sum := sum[0 := sum[0] + 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists i₉: int ::
                      i₉ < N
                      && x₁₀ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && a[x₁₀] == sum[0])))
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
               ==> i₉ < N));
  {
    a := a[i := sum[0]];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < N));
  {
    assert a[i] == N;
    i := i + 1;
  }
  c#result := 1;
  return;
}

