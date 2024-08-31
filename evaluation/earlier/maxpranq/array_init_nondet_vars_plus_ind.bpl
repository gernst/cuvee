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
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₂: int ::
            ((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
               ==> (exists x₉: int, y₁₀: int, i₁₁: int ::
                      y₁₀ < x₉
                      && y₁₀ < 100000
                      && -100000 < y₁₀
                      && x₉ < 100000
                      && -100000 < x₉
                      && i₁₁ < N
                      && x₁₂ == i₁₁
                      && old(i) <= i₁₁
                      && i₁₁ < i
                      && a[x₁₂] == y₁₀)))
      && (forall x₁₂: int ::
            (!((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
            )
               ==> a[x₁₂] == old(a[x₁₂])))
      && (forall x₁₃: int ::
            ((exists i₁₁: int ::
                    x₁₃ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
               ==> (exists x₉: int, y₁₀: int, i₁₁: int ::
                      y₁₀ < x₉
                      && y₁₀ < 100000
                      && -100000 < y₁₀
                      && x₉ < 100000
                      && -100000 < x₉
                      && i₁₁ < N
                      && x₁₃ == i₁₁
                      && old(i) <= i₁₁
                      && i₁₁ < i
                      && b[x₁₃] == x₉)))
      && (forall x₁₃: int ::
            (!((exists i₁₁: int ::
                    x₁₃ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
            )
               ==> b[x₁₃] == old(b[x₁₃])))
      && (forall i₁₁: int ::
            (  old(i₁₁) <= i₁₁
              && old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < N));
  {
    var x: int;
    var y: int;
    assume x < 100000 && -100000 < x;
    assume y < 100000 && -100000 < y;
    assume y < x;
    a := a[i := y];
    b := b[i := x];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₈: int ::
            ((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
               ==> (exists i₁₇: int ::
                      i₁₇ < N
                      && x₁₈ == i₁₇
                      && old(i) <= i₁₇
                      && i₁₇ < i
                      && c[x₁₈] == a[i₁₇] + -b[i₁₇])))
      && (forall x₁₈: int ::
            (!((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
            )
               ==> c[x₁₈] == old(c[x₁₈])))
      && (forall i₁₇: int ::
            (  old(i₁₇) <= i₁₇
              && old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < N));
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
      && (forall i₂₁: int ::
            (  old(i₂₁) <= i₂₁
              && old(i) <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < N));
  {
    assert c[i] < 0;
    i := i + 1;
  }
}

