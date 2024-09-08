data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var N: int;
  var a: [int]int;
  assume 0 < N;
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ < N
                && a[i₇] == 1))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> a[i₇] == old(a)[i₇]));
  {
    a := a[i := 1];
    i := i + 1;
  }
  i := N - 1;
  while(0 <= i)
    decreases i + 1 - 0;
    invariant i <= old(i)
      && 0 <= 1 + i
      && (forall i₁₀: int ::
            (  i < i₁₀
              && i₁₀ <= old(i)
               ==> 0 <= i₁₀
                && a[i₁₀] == -1 + old(a)[i₁₀]))
      && (forall i₁₀: int ::
            (!(  i < i₁₀
              && i₁₀ <= old(i)
            )
               ==> a[i₁₀] == old(a)[i₁₀]));
  {
    a := a[i := a[i] - 1];
    i := i - 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < N));
  {
    assert a[i] == 0;
    i := i + 1;
  }
}

