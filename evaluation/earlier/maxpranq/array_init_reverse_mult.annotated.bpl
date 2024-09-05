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
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₈: int ::
            ((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists i₇: int ::
                      i₇ < N
                      && x₈ == i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && a[x₈] == 1)))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> a[x₈] == old(a[x₈])))
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ < N));
  {
    a := a[i := 1];
    i := i + 1;
  }
  i := N - 1;
  while(0 <= i)
    decreases i + 1 - 0;
    invariant true
      && i <= old(i)
      && 0 <= 1 + i
      && (forall x₁₂: int ::
            ((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && i < i₁₁
                    && i₁₁ <= old(i))
               ==> (exists i₁₁: int ::
                      0 <= i₁₁
                      && x₁₂ == i₁₁
                      && i < i₁₁
                      && i₁₁ <= old(i)
                      && a[x₁₂] == -1 + old(a)[i₁₁])))
      && (forall x₁₂: int ::
            (!((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && i < i₁₁
                    && i₁₁ <= old(i))
            )
               ==> a[x₁₂] == old(a[x₁₂])))
      && (forall i₁₁: int ::
            (  i < i₁₁
              && i₁₁ <= old(i)
               ==> 0 <= i₁₁));
  {
    a := a[i := a[i] - 1];
    i := i - 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₁₅: int ::
            (  old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < N));
  {
    assert a[i] == 0;
    i := i + 1;
  }
}

