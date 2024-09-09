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
  var N: int;
  var a: [int]int;
  var b: [int]int;
  assume 0 < N;
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> (exists j₈: int, k₉: int ::
                      j₈ <= k₉
                      && -10000 < k₉
                      && k₉ < 10000
                      && -10000 < j₈
                      && j₈ < 10000
                      && i₁₀ < N
                      && a[i₁₀] == k₉
                      && b[i₁₀] == j₈)))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> a[i₁₀] == old(a)[i₁₀]
                && b[i₁₀] == old(b)[i₁₀]));
  {
    var j: int;
    var k: int;
    assume -10000 < j && j < 10000;
    assume -10000 < k && k < 10000;
    assume j <= k;
    a := a[i := k];
    b := b[i := j];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < N
                && a[i₁₄] == 1 + old(a)[i₁₄]
                && b[i₁₄] == 1 + old(b)[i₁₄]))
      && (forall i₁₄: int ::
            (!(  old(i) <= i₁₄
              && i₁₄ < i
            )
               ==> a[i₁₄] == old(a)[i₁₄]
                && b[i₁₄] == old(b)[i₁₄]));
  {
    a := a[i := a[i] + 1];
    b := b[i := b[i] + 1];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < N));
  {
    assert b[i] <= a[i];
    i := i + 1;
  }
}

