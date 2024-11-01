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
  N := 1000000;
  var i: int;
  var j: int := 0;
  var a: [int]int;
  var R: int := 5;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₃: int ::
            (  old(i) <= i₃
              && i₃ < i
               ==> N / 2 < i₃
                  && i₃ < N
                  && a[i₃] == i₃ % R
                ||   !(N / 2 < i₃
                  )
                  && i₃ < N
                  && a[i₃] == 1 + i₃))
      && (forall i₃: int ::
            (!(  old(i) <= i₃
              && i₃ < i
            )
               ==> a[i₃] == old(a)[i₃]));
  {
    a[i] := i + 1;
    if(N / 2 < i) {
      a[i] := i % R;
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant j + old(j) == i + old(i)
      && old(j) <= j
      && old(i) <= i
      && (forall j₆: int, i₇: int ::
            (  old(j₆) + j₆ == i₇ + old(i₇)
              && old(j) <= j₆
              && j₆ < j
              && old(i) <= i₇
              && i₇ < i
               ==> a[i₇] == 0
                  && i₇ < N
                ||   a[i₇] != 0
                  && i₇ < N));
  {
    if(a[i] == 0) {
      j := j + 1;
    }
    assert j < N / 10;
    i := i + 1;
  }
  c#result := 0;
  return;
}

