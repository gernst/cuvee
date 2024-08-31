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
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists x₈: int, i₉: int ::
                      x₈ < 10000
                      && i₉ < N
                      && x₁₀ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && a[x₁₀] == x₈)))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> a[x₁₀] == old(a[x₁₀])))
      && (forall x₁₁: int ::
            ((exists i₉: int ::
                    x₁₁ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists x₈: int, i₉: int ::
                      x₈ < 10000
                      && i₉ < N
                      && x₁₁ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && b[x₁₁] == -x₈)))
      && (forall x₁₁: int ::
            (!((exists i₉: int ::
                    x₁₁ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> b[x₁₁] == old(b[x₁₁])))
      && (forall i₉: int ::
            (  old(i₉) <= i₉
              && old(i) <= i₉
              && i₉ < i
               ==> i₉ < N));
  {
    var x: int;
    assume x < 10000;
    a := a[i := x];
    b := b[i := -x];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₆: int ::
            ((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
               ==> (exists i₁₅: int ::
                      i₁₅ < N
                      && x₁₆ == i₁₅
                      && old(i) <= i₁₅
                      && i₁₅ < i
                      && a[x₁₆] == -old(b)[i₁₅])))
      && (forall x₁₆: int ::
            (!((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
            )
               ==> a[x₁₆] == old(a[x₁₆])))
      && (forall x₁₇: int ::
            ((exists i₁₅: int ::
                    x₁₇ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
               ==> (exists i₁₅: int ::
                      i₁₅ < N
                      && x₁₇ == i₁₅
                      && old(i) <= i₁₅
                      && i₁₅ < i
                      && b[x₁₇] == old(a)[i₁₅])))
      && (forall x₁₇: int ::
            (!((exists i₁₅: int ::
                    x₁₇ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
            )
               ==> b[x₁₇] == old(b[x₁₇])))
      && (forall i₁₅: int ::
            (  old(i₁₅) <= i₁₅
              && old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < N));
  {
    var tmp: int := a[i];
    a := a[i := -b[i]];
    b := b[i := tmp];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₂₁: int ::
            (  old(i₂₁) <= i₂₁
              && old(i) <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < N));
  {
    assert a[i] == b[i];
    i := i + 1;
  }
}

