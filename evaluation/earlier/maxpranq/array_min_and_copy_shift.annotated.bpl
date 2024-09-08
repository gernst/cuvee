data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var j: int;
  var N: int;
  var a: [int]int;
  var b: [int]int;
  assume 0 < N;
  assume j < 10000 && -10000 < j;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> (exists k₉: int ::
                      j <= k₉
                      && k₉ < 10000
                      && -10000 < k₉
                      && i₁₀ < N
                      && a[i₁₀] == k₉)))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> a[i₁₀] == old(a)[i₁₀]));
  {
    var k: int;
    assume k < 10000 && -10000 < k;
    assume j <= k;
    a := a[i := k];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < N
                && b[i₁₃] == -j + a[i₁₃]))
      && (forall i₁₃: int ::
            (!(  old(i) <= i₁₃
              && i₁₃ < i
            )
               ==> b[i₁₃] == old(b)[i₁₃]));
  {
    b := b[i := a[i] - j];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < N));
  {
    assert 0 <= b[i];
    i := i + 1;
  }
}

