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
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
               ==> (exists i₅: int ::
                        i₅ % 1 == 0
                        && i₅ < N
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i
                        && a[x₆] == 1)
                || (exists i₅: int ::
                        i₅ % 1 != 0
                        && i₅ < N
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i
                        && a[x₆] == 0)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall i₅: int ::
            (  0 <= i₅
              && i₅ < i
               ==> i₅ < N));
  {
    if(i % 1 == 0) {
      a := a[i := 1];
    } else {
      a := a[i := 0];
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
            (x₁₀ == 0
               ==> (exists i₉: int ::
                        i₉ == 0
                        && i₉ < N
                        && x₁₀ == 0
                        && sum[x₁₀] == 10 + N / 2)
                || (exists i₉: int ::
                        i₉ != 0
                        && i₉ < N
                        && x₁₀ == 0
                        && sum[x₁₀] == old(sum)[0] + a[i₉])))
      && (forall x₁₀: int ::
            (x₁₀ != 0
               ==> sum[x₁₀] == old(sum[x₁₀])))
      && (forall i₉: int ::
            (  0 <= i₉
              && i₉ < i
               ==> i₉ < N));
  {
    if(i == 0) {
      sum := sum[0 := N / 2 + 10];
    } else {
      sum := sum[0 := sum[0] + a[i]];
    }
    i := i + 1;
  }
  assert sum[0] <= N;
  c#result := 1;
  return;
}

