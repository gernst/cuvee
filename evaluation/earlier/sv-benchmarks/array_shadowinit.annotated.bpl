data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  N := 0;
  havoc N;
  assume -2147483648 <= N && N < 2147483648;
  if(0 < N) {
    var i: int;
    var k: int;
    var a: [int]int;
    i := 0;
    k := 0;
    while(i < N)
      decreases N - i;
      invariant i + old(i) == old(k) + k
        && old(i) <= i
        && old(k) <= k
        && (forall i₅: int, k₆: int ::
              (  i₅ + old(i₅) == k₆ + old(k₆)
                && old(i) <= i₅
                && i₅ < i
                && old(k) <= k₆
                && k₆ < k
                 ==> i₅ < N
                  && a[k₆] == k₆))
        && (forall i₅: int, k₆: int ::
              (  i₅ + old(i₅) == k₆ + old(k₆)
                && !(  old(i) <= i₅
                  && i₅ < i
                  && old(k) <= k₆
                  && k₆ < k
                )
                 ==> a[k₆] == old(a)[k₆]));
    {
      a[k] := k;
      i := i + 1;
      k := k + 1;
    }
    i := 0;
    while(i < N)
      decreases N - i;
      invariant old(i) <= i
        && (forall i₁₀: int ::
              (  old(i) <= i₁₀
                && i₁₀ < i
                 ==> i₁₀ < N));
    {
      assert a[i] == i;
      i := i + 1;
    }
  }
  c#result := 0;
  return;
}

