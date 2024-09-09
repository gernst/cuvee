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
                && a[i₄] == 0))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> a[i₄] == old(a)[i₄]));
  {
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> N % 2 == 0
                  && i₇ < N
                  && a[i₇] == 2 + old(a)[i₇]
                ||   N % 2 != 0
                  && i₇ < N
                  && a[i₇] == 1 + old(a)[i₇]))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> a[i₇] == old(a)[i₇]));
  {
    if(N % 2 == 0) {
      a := a[i := a[i] + 2];
    } else {
      a := a[i := a[i] + 1];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < N));
  {
    assert a[i] % 2 == N % 2;
    i := i + 1;
  }
  c#result := 1;
  return;
}

