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
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < N
                && a[i₄] == 1 + i₄ * i₄ + -2 * i₄))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> a[i₄] == old(a)[i₄]));
  {
    a := a[i := (i - 1) * (i - 1)];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ < N
                && a[i₇] == old(a)[i₇] + i₇))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> a[i₇] == old(a)[i₇]));
  {
    a := a[i := a[i] + i];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < N
                && a[i₁₀] == old(a)[i₁₀] + i₁₀))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> a[i₁₀] == old(a)[i₁₀]));
  {
    a := a[i := a[i] + i];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < N
                && a[i₁₃] == -1 + old(a)[i₁₃]))
      && (forall i₁₃: int ::
            (!(  old(i) <= i₁₃
              && i₁₃ < i
            )
               ==> a[i₁₃] == old(a)[i₁₃]));
  {
    a := a[i := a[i] - 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < N));
  {
    assert a[i] == i * i;
    i := i + 1;
  }
  c#result := 1;
  return;
}

