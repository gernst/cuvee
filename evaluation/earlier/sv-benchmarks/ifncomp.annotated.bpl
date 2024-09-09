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
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> i₆ == 0
                  && i₆ < N
                  && a[0] == 6
                ||   i₆ != 0
                  && i₆ < N
                  && a[i₆] == 6 + old(a)[-1 + i₆]))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> a[0] == old(a)[0]
                && a[i₆] == old(a)[i₆]));
  {
    if(i == 0) {
      a := a[0 := 6];
    } else {
      a := a[i := a[i - 1] + 6];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ == 0
                  && i₉ < N
                  && b[0] == 1
                ||   i₉ != 0
                  && i₉ < N
                  && b[i₉] == old(b)[-1 + i₉] + a[-1 + i₉]))
      && (forall i₉: int ::
            (!(  old(i) <= i₉
              && i₉ < i
            )
               ==> b[0] == old(b)[0]
                && b[i₉] == old(b)[i₉]));
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
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ == 0
                  && i₁₂ < N
                  && c[0] == N
                ||   i₁₂ != 0
                  && i₁₂ < N
                  && c[i₁₂] == old(c)[-1 + i₁₂] + b[-1 + i₁₂]))
      && (forall i₁₂: int ::
            (!(  old(i) <= i₁₂
              && i₁₂ < i
            )
               ==> c[0] == old(c)[0]
                && c[i₁₂] == old(c)[i₁₂]));
  {
    if(i == 0) {
      c := c[0 := N];
    } else {
      c := c[i := c[i - 1] + b[i - 1]];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₅: int ::
            (  old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < N));
  {
    assert c[i] == N + i * i * i;
    i := i + 1;
  }
  c#result := 1;
  return;
}

