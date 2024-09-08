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
      && i <= N
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> (exists j₈: int ::
                      1 <= j₈
                      && i₉ < N
                      && a[i₉] == j₈)))
      && (forall i₉: int ::
            (!(  old(i) <= i₉
              && i₉ < i
            )
               ==> a[i₉] == old(a)[i₉]));
  {
    var j: int;
    assume 1 <= j;
    a := a[i := j];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < N
                && b[i₁₂] == a[i₁₂]))
      && (forall i₁₂: int ::
            (!(  old(i) <= i₁₂
              && i₁₂ < i
            )
               ==> b[i₁₂] == old(b)[i₁₂]));
  {
    b := b[i := a[i]];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₁₅: int ::
            (  old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < N));
  {
    assert 1 <= b[i];
    i := i + 1;
  }
}

