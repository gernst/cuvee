data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  N := 100000;
  var a: [int]int;
  var b: [int]int;
  var i: int;
  var sum: int := 0;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < N
                && a[i₄] == i₄))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> a[i₄] == old(a)[i₄]));
  {
    a[i] := i;
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
                && b[-1 + N + -i₇] == i₇))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> b[-1 + N + -i₇] == old(b)[-1 + N + -i₇]));
  {
    b[((N - i) - 1)] := i;
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < N));
  {
    sum := sum + a[i] - b[N - i - 1];
    i := i + 1;
  }
  assert sum == 0;
  c#result := 0;
  return;
}

