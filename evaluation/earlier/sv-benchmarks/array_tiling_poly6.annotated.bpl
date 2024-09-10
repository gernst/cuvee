data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var S: int;
  assume -2147483648 <= S && S < 2147483648;
  assume 1 < S;
  var i: int;
  var a: [int]int;
  i := 0;
  while(i < S)
    decreases S - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < S
                && a[i₄] == -1 + i₄ * i₄))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> a[i₄] == old(a)[i₄]));
  {
    a[i] := (i - 1) * (i + 1);
    i := i + 1;
  }
  i := 0;
  while(i < S)
    decreases S - i;
    invariant old(i) <= i
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ < S
                && a[i₇] == old(a)[i₇] + -(i₇ * i₇)))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> a[i₇] == old(a)[i₇]));
  {
    a[i] := a[i] - i * i;
    i := i + 1;
  }
  i := 0;
  while(i < S)
    decreases S - i;
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < S));
  {
    assert a[i] == -1;
    i := i + 1;
  }
  c#result := 0;
  return;
}

