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
  var c: [int]int;
  assume 0 < N;
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> (exists j₉: int, k₁₀: int ::
                      j₉ + k₁₀ == 0
                      && -10000 < k₁₀
                      && k₁₀ < 10000
                      && -10000 < j₉
                      && j₉ < 10000
                      && i₁₁ < N
                      && a[i₁₁] == j₉
                      && b[i₁₁] == k₁₀)))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> a[i₁₁] == old(a)[i₁₁]
                && b[i₁₁] == old(b)[i₁₁]));
  {
    var j: int;
    var k: int;
    assume -10000 < j && j < 10000;
    assume -10000 < k && k < 10000;
    assume j + k == 0;
    a := a[i := j];
    b := b[i := k];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₅: int ::
            (  old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < N
                && c[i₁₅] == a[i₁₅] + b[i₁₅]))
      && (forall i₁₅: int ::
            (!(  old(i) <= i₁₅
              && i₁₅ < i
            )
               ==> c[i₁₅] == old(c)[i₁₅]));
  {
    c := c[i := a[i] + b[i]];
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
    assert c[i] == 0;
    i := i + 1;
  }
}

