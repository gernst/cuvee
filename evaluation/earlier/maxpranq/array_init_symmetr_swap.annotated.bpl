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
  var i: int;
  var N: int;
  var a: [int]int;
  var b: [int]int;
  assume 0 < N;
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> (exists x₈: int ::
                      x₈ < 10000
                      && i₉ < N
                      && a[i₉] == x₈
                      && b[i₉] == -x₈)))
      && (forall i₉: int ::
            (!(  old(i) <= i₉
              && i₉ < i
            )
               ==> a[i₉] == old(a)[i₉]
                && b[i₉] == old(b)[i₉]));
  {
    var x: int;
    assume x < 10000;
    a[i] := x;
    b[i] := -x;
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
                && a[i₁₃] == -old(b)[i₁₃]
                && b[i₁₃] == old(a)[i₁₃]))
      && (forall i₁₃: int ::
            (!(  old(i) <= i₁₃
              && i₁₃ < i
            )
               ==> a[i₁₃] == old(a)[i₁₃]
                && b[i₁₃] == old(b)[i₁₃]));
  {
    var tmp: int := a[i];
    a[i] := -b[i];
    b[i] := tmp;
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < N));
  {
    assert a[i] == b[i];
    i := i + 1;
  }
}

