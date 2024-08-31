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
  assume N < 100000 && 0 < N;
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
               ==> (exists x₉: int, i₁₀: int ::
                      x₉ < 100000
                      && -100000 < x₉
                      && i₁₀ < N
                      && x₁₁ == i₁₀
                      && old(i) <= i₁₀
                      && i₁₀ < i
                      && a[x₁₁] == x₉ + N)))
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
               ==> (exists x₉: int, i₁₀: int ::
                      x₉ < 100000
                      && -100000 < x₉
                      && i₁₀ < N
                      && x₁₂ == i₁₀
                      && old(i) <= i₁₀
                      && i₁₀ < i
                      && b[x₁₂] == x₉)))
      && (forall x₁₂: int ::
            (!((exists i₁₀: int ::
                    x₁₂ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
            )
               ==> b[x₁₂] == old(b[x₁₂])))
      && (forall i₁₀: int ::
            (  old(i₁₀) <= i₁₀
              && old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < N));
  {
    var x: int;
    assume x < 100000 && -100000 < x;
    a := a[i := N + x];
    b := b[i := x];
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
                      && c[x₁₇] == a[i₁₆] + -b[i₁₆])))
      && (forall x₁₇: int ::
            (!((exists i₁₆: int ::
                    x₁₇ == i₁₆
                    && old(i) <= i₁₆
                    && i₁₆ < i)
            )
               ==> c[x₁₇] == old(c[x₁₇])))
      && (forall i₁₆: int ::
            (  old(i₁₆) <= i₁₆
              && old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < N));
  {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₂₀: int ::
            (  old(i₂₀) <= i₂₀
              && old(i) <= i₂₀
              && i₂₀ < i
               ==> i₂₀ < N));
  {
    assert c[i] == N;
    i := i + 1;
  }
}

