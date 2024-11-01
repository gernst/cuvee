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
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> (exists x₅: int ::
                      -100000 < x₅
                      && x₅ < 100000
                      && -2147483648 <= x₅
                      && x₅ < 2147483648
                      && i₆ < N
                      && a[i₆] == x₅
                      && b[i₆] == -x₅)))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> a[i₆] == old(a)[i₆]
                && b[i₆] == old(b)[i₆]));
  {
    var x: int;
    assume -2147483648 <= x && x < 2147483648;
    assume -100000 < x && x < 100000;
    a[i] := x;
    b[i] := -x;
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
                && c[i₁₀] == b[i₁₀] + a[i₁₀]))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> c[i₁₀] == old(c)[i₁₀]));
  {
    c[i] := a[i] + b[i];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < N));
  {
    assert c[i] == 0;
    i := i + 1;
  }
  c#result := 0;
  return;
}

