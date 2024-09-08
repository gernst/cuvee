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
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ == 0
                  && i₅ < N
                  && a[0] == 10
                ||   i₅ != 0
                  && i₅ < N
                  && a[i₅] == 10 + old(a)[-1 + i₅]))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[0] == old(a)[0]
                && a[i₅] == old(a)[i₅]));
  {
    if(i == 0) {
      a := a[0 := 10];
    } else {
      a := a[i := a[i - 1] + 10];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ == 0
                  && i₈ < N
                  && b[0] == 1
                ||   i₈ != 0
                  && i₈ < N
                  && b[i₈] == old(b)[-1 + i₈] + a[-1 + i₈]))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> b[0] == old(b)[0]
                && b[i₈] == old(b)[i₈]));
  {
    if(i == 0) {
      b := b[0 := 1];
    } else {
      b := b[i := b[i - 1] + a[i - 1]];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < N));
  {
    assert b[i] == 5 * i * i + 5 * i + 1;
    i := i + 1;
  }
  c#result := 1;
  return;
}

