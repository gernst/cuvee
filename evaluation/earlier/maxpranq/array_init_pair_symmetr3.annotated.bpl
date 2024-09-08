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
    invariant old(i) <= i
      && i <= N
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> (exists x₉: int ::
                      x₉ < 100000
                      && -100000 < x₉
                      && i₁₀ < N
                      && a[i₁₀] == x₉ + N
                      && b[i₁₀] == x₉)))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> a[i₁₀] == old(a)[i₁₀]
                && b[i₁₀] == old(b)[i₁₀]));
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
    invariant old(i) <= i
      && i <= N
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < N
                && c[i₁₄] == a[i₁₄] + -b[i₁₄]))
      && (forall i₁₄: int ::
            (!(  old(i) <= i₁₄
              && i₁₄ < i
            )
               ==> c[i₁₄] == old(c)[i₁₄]));
  {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < N));
  {
    assert c[i] == N;
    i := i + 1;
  }
}

