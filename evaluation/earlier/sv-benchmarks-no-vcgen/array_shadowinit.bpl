data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  havoc N;
  if(0 < N) {
    var i: int;
    var k: int;
    var a: [int]int;
    i := 0;
    k := 0;
    while(i < N)
      decreases N - i;
      invariant true
        && 0 <= i
        && 0 <= k
        && i <= N
        && (forall x₇: int ::
              ((exists k₆: int ::
                      x₇ == k₆
                      && 0 <= k₆
                      && k₆ < k)
                 ==> (exists i₅: int, k₆: int ::
                        i₅ < N
                        && x₇ == k₆
                        && 0 <= k₆
                        && k₆ < k
                        && a[x₇] == k₆)))
        && (forall x₇: int ::
              (!((exists k₆: int ::
                      x₇ == k₆
                      && 0 <= k₆
                      && k₆ < k)
              )
                 ==> a[x₇] == old(a[x₇])))
        && (forall i₅: int, k₆: int ::
              (  0 <= i₅
                && 0 <= k₆
                && i₅ < i
                && k₆ < k
                 ==> i₅ < N));
    {
      a := a[k := k];
      i := i + 1;
      k := k + 1;
    }
    i := 0;
    while(i < N)
      decreases N - i;
      invariant true
        && 0 <= i
        && i <= N
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i
                 ==> i₁₁ < N));
    {
      assert a[i] == i;
      i := i + 1;
    }
  }
  c#result := 0;
  return;
}

