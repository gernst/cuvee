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
  var i: int;
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> (exists x₅: int, y₆: int ::
                      y₆ < x₅
                      && x₅ < 100000
                      && -100000 < x₅
                      && y₆ < 100000
                      && -100000 < y₆
                      && -2147483648 <= y₆
                      && y₆ < 2147483648
                      && -2147483648 <= x₅
                      && x₅ < 2147483648
                      && i₇ < N
                      && a[i₇] == x₅
                      && b[i₇] == y₆)))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> a[i₇] == old(a)[i₇]
                && b[i₇] == old(b)[i₇]));
  {
    var x: int;
    assume -2147483648 <= x && x < 2147483648;
    var y: int;
    assume -2147483648 <= y && y < 2147483648;
    assume y < 100000 && -100000 < y;
    assume x < 100000 && -100000 < x;
    assume y < x;
    a[i] := x;
    b[i] := y;
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < N
                && c[i₁₁] == -b[i₁₁] + a[i₁₁]))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> c[i₁₁] == old(c)[i₁₁]));
  {
    c[i] := a[i] - b[i];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < N));
  {
    assert 0 < c[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

