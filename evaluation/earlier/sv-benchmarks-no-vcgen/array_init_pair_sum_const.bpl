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
  var N: int := 100000;
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
               ==> (exists i₅: int ::
                      i₅ < N
                      && x₆ == i₅
                      && 0 <= i₅
                      && i₅ < i
                      && a[x₆] == 1)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall x₇: int ::
            ((exists i₅: int ::
                    x₇ == i₅
                    && 0 <= i₅
                    && i₅ < i)
               ==> (exists i₅: int ::
                      i₅ < N
                      && x₇ == i₅
                      && 0 <= i₅
                      && i₅ < i
                      && b[x₇] == 2)))
      && (forall x₇: int ::
            (!((exists i₅: int ::
                    x₇ == i₅
                    && 0 <= i₅
                    && i₅ < i)
            )
               ==> b[x₇] == old(b[x₇])))
      && (forall i₅: int ::
            (  0 <= i₅
              && i₅ < i
               ==> i₅ < N));
  {
    a := a[i := 1];
    b := b[i := 2];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₁₂: int ::
            ((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && 0 <= i₁₁
                    && i₁₁ < i)
               ==> (exists i₁₁: int ::
                      i₁₁ < N
                      && x₁₂ == i₁₁
                      && 0 <= i₁₁
                      && i₁₁ < i
                      && c[x₁₂] == b[i₁₁] + a[i₁₁])))
      && (forall x₁₂: int ::
            (!((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && 0 <= i₁₁
                    && i₁₁ < i)
            )
               ==> c[x₁₂] == old(c[x₁₂])))
      && (forall i₁₁: int ::
            (  0 <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < N));
  {
    c := c[i := a[i] + b[i]];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && 1 <= i
      && i <= N
      && (forall i₁₅: int ::
            (  1 <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < N));
  {
    assert 3 <= c[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

