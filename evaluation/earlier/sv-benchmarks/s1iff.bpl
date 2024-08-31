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
  sum := sum[0 := 1];
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
               ==> (exists i₅: int ::
                      i₅ < N
                      && x₆ == i₅
                      && old(i) <= i₅
                      && i₅ < i
                      && a[x₆] == 1)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall i₅: int ::
            (  old(i₅) <= i₅
              && old(i) <= i₅
              && i₅ < i
               ==> i₅ < N));
  {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₀: int ::
            (x₁₀ == 0
               ==> (exists i₉: int ::
                        a[i₉] == 1
                        && i₉ < N
                        && x₁₀ == 0
                        && sum[x₁₀] == a[i₉] + old(sum)[0])
                || (exists i₉: int ::
                        a[i₉] != 1
                        && i₉ < N
                        && x₁₀ == 0
                        && sum[x₁₀] == old(sum)[0] * a[i₉])))
      && (forall x₁₀: int ::
            (x₁₀ != 0
               ==> sum[x₁₀] == old(sum[x₁₀])))
      && (forall i₉: int ::
            (  old(i₉) <= i₉
              && old(i) <= i₉
              && i₉ < i
               ==> i₉ < N));
  {
    if(a[i] == 1) {
      sum := sum[0 := sum[0] + a[i]];
    } else {
      sum := sum[0 := sum[0] * a[i]];
    }
    i := i + 1;
  }
  assert sum[0] == 2 * N;
  c#result := 1;
  return;
}

