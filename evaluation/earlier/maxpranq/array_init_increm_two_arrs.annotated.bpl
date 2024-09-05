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
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₁: int ::
            ((exists i₁₀: int ::
                    x₁₁ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
               ==> (exists j₈: int, k₉: int, i₁₀: int ::
                      j₈ <= k₉
                      && -10000 < k₉
                      && k₉ < 10000
                      && -10000 < j₈
                      && j₈ < 10000
                      && i₁₀ < N
                      && x₁₁ == i₁₀
                      && old(i) <= i₁₀
                      && i₁₀ < i
                      && a[x₁₁] == k₉)))
      && (forall x₁₁: int ::
            (!((exists i₁₀: int ::
                    x₁₁ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
            )
               ==> a[x₁₁] == old(a[x₁₁])))
      && (forall x₁₂: int ::
            ((exists i₁₀: int ::
                    x₁₂ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
               ==> (exists j₈: int, k₉: int, i₁₀: int ::
                      j₈ <= k₉
                      && -10000 < k₉
                      && k₉ < 10000
                      && -10000 < j₈
                      && j₈ < 10000
                      && i₁₀ < N
                      && x₁₂ == i₁₀
                      && old(i) <= i₁₀
                      && i₁₀ < i
                      && b[x₁₂] == j₈)))
      && (forall x₁₂: int ::
            (!((exists i₁₀: int ::
                    x₁₂ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
            )
               ==> b[x₁₂] == old(b[x₁₂])))
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < N));
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
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₇: int ::
            ((exists i₁₆: int ::
                    x₁₇ == i₁₆
                    && old(i) <= i₁₆
                    && i₁₆ < i)
               ==> (exists i₁₆: int ::
                      i₁₆ < N
                      && x₁₇ == i₁₆
                      && old(i) <= i₁₆
                      && i₁₆ < i
                      && a[x₁₇] == 1 + old(a)[i₁₆])))
      && (forall x₁₇: int ::
            (!((exists i₁₆: int ::
                    x₁₇ == i₁₆
                    && old(i) <= i₁₆
                    && i₁₆ < i)
            )
               ==> a[x₁₇] == old(a[x₁₇])))
      && (forall x₁₈: int ::
            ((exists i₁₆: int ::
                    x₁₈ == i₁₆
                    && old(i) <= i₁₆
                    && i₁₆ < i)
               ==> (exists i₁₆: int ::
                      i₁₆ < N
                      && x₁₈ == i₁₆
                      && old(i) <= i₁₆
                      && i₁₆ < i
                      && b[x₁₈] == 1 + old(b)[i₁₆])))
      && (forall x₁₈: int ::
            (!((exists i₁₆: int ::
                    x₁₈ == i₁₆
                    && old(i) <= i₁₆
                    && i₁₆ < i)
            )
               ==> b[x₁₈] == old(b[x₁₈])))
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < N));
  {
    a := a[i := a[i] + 1];
    b := b[i := b[i] + 1];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₂₂: int ::
            (  old(i) <= i₂₂
              && i₂₂ < i
               ==> i₂₂ < N));
  {
    assert b[i] <= a[i];
    i := i + 1;
  }
}

