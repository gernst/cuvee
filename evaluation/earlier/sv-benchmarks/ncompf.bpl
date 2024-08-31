data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  havoc N;
  if(N <= 0) {
    c#result := 1;
    return;
  }
  assume N <= 2147483647 / 4;
  var i: int;
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  a := a[0 := 6];
  b := b[0 := 1];
  c := c[0 := 0];
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₇: int ::
            ((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
               ==> (exists i₆: int ::
                      i₆ < N
                      && x₇ == i₆
                      && old(i) <= i₆
                      && i₆ < i
                      && a[x₇] == 6 + old(a)[-1 + i₆])))
      && (forall x₇: int ::
            (!((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
            )
               ==> a[x₇] == old(a[x₇])))
      && (forall i₆: int ::
            (  old(i₆) <= i₆
              && old(i) <= i₆
              && i₆ < i
               ==> i₆ < N));
  {
    a := a[i := a[i - 1] + 6];
    i := i + 1;
  }
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
               ==> (exists i₁₀: int ::
                      i₁₀ < N
                      && x₁₁ == i₁₀
                      && old(i) <= i₁₀
                      && i₁₀ < i
                      && b[x₁₁] == old(b)[-1 + i₁₀] + a[-1 + i₁₀])))
      && (forall x₁₁: int ::
            (!((exists i₁₀: int ::
                    x₁₁ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
            )
               ==> b[x₁₁] == old(b[x₁₁])))
      && (forall i₁₀: int ::
            (  old(i₁₀) <= i₁₀
              && old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < N));
  {
    b := b[i := b[i - 1] + a[i - 1]];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₅: int ::
            ((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
               ==> (exists i₁₄: int ::
                      i₁₄ < N
                      && x₁₅ == i₁₄
                      && old(i) <= i₁₄
                      && i₁₄ < i
                      && c[x₁₅] == b[-1 + i₁₄] + old(c)[-1 + i₁₄])))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
            )
               ==> c[x₁₅] == old(c[x₁₅])))
      && (forall i₁₄: int ::
            (  old(i₁₄) <= i₁₄
              && old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < N));
  {
    c := c[i := c[i - 1] + b[i - 1]];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₁₈: int ::
            (  old(i₁₈) <= i₁₈
              && old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < N));
  {
    assert c[i] == N + i * i * i;
    i := i + 1;
  }
  c#result := 1;
  return;
}

