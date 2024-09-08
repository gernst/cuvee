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
    invariant old(i) <= i
      && i <= N
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ % 3 == 0
                  && i₅ < N
                  && a[i₅] == 3
                ||   i₅ % 3 != 0
                  && i₅ < N
                  && a[i₅] == 0))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]));
  {
    if(i % 3 == 0) {
      a := a[i := 3];
    } else {
      a := a[i := 0];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ == 0
                  && i₈ < N
                  && sum[0] == 0
                ||   i₈ != 0
                  && i₈ < N
                  && sum[0] == a[i₈] + old(sum)[0]))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    if(i == 0) {
      sum := sum[0 := 0];
    } else {
      sum := sum[0 := sum[0] + a[i]];
    }
    i := i + 1;
  }
  assert sum[0] <= 3 * N;
  c#result := 1;
  return;
}

