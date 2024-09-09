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
  assume 0 < N;
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> (exists j₇: int ::
                      0 <= j₇
                      && j₇ < 10000
                      && i₈ < N
                      && a[i₈] == j₇)))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> a[i₈] == old(a)[i₈]));
  {
    var j: int;
    assume 0 <= j && j < 10000;
    a := a[i := j];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < N
                && a[i₁₁] == 1 + old(a)[i₁₁]))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> a[i₁₁] == old(a)[i₁₁]));
  {
    a := a[i := a[i] + 1];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < N));
  {
    assert 1 <= a[i];
    i := i + 1;
  }
}

