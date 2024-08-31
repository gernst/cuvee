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
      && (forall x₉: int ::
            ((exists i₈: int ::
                    x₉ == i₈
                    && old(i) <= i₈
                    && i₈ < i)
               ==> (exists j₇: int, i₈: int ::
                      i₈ <= j₇
                      && -10000 < j₇
                      && j₇ < 10000
                      && i₈ < N
                      && x₉ == i₈
                      && old(i) <= i₈
                      && i₈ < i
                      && a[x₉] == j₇)))
      && (forall x₉: int ::
            (!((exists i₈: int ::
                    x₉ == i₈
                    && old(i) <= i₈
                    && i₈ < i)
            )
               ==> a[x₉] == old(a[x₉])))
      && (forall i₈: int ::
            (  old(i₈) <= i₈
              && old(i) <= i₈
              && i₈ < i
               ==> i₈ < N));
  {
    var j: int;
    assume -10000 < j && j < 10000;
    assume i <= j;
    a := a[i := j];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₃: int ::
            ((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && old(i) <= i₁₂
                    && i₁₂ < i)
               ==> (exists i₁₂: int ::
                      i₁₂ < N
                      && x₁₃ == i₁₂
                      && old(i) <= i₁₂
                      && i₁₂ < i
                      && a[x₁₃] == old(a)[i₁₂] + i₁₂)))
      && (forall x₁₃: int ::
            (!((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && old(i) <= i₁₂
                    && i₁₂ < i)
            )
               ==> a[x₁₃] == old(a[x₁₃])))
      && (forall i₁₂: int ::
            (  old(i₁₂) <= i₁₂
              && old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < N));
  {
    a := a[i := i + a[i]];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₁₆: int ::
            (  old(i₁₆) <= i₁₆
              && old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < N));
  {
    assert 2 * i <= a[i];
    i := i + 1;
  }
}

