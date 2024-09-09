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
  var sum: [int]int;
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  sum := sum[0 := 0];
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
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
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < N
                && b[i₁₀] == 1))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> b[i₁₀] == old(b)[i₁₀]));
  {
    b := b[i := 1];
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
                && c[i₁₃] == 1))
      && (forall i₁₃: int ::
            (!(  old(i) <= i₁₃
              && i₁₃ < i
            )
               ==> c[i₁₃] == old(c)[i₁₃]));
  {
    c := c[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < N
                && sum[0] == a[i₁₆] + old(sum)[0]))
      && (forall i₁₆: int ::
            (!(  old(i) <= i₁₆
              && i₁₆ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    sum := sum[0 := sum[0] + a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₉: int ::
            (  old(i) <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < N
                && sum[0] == b[i₁₉] + old(sum)[0]))
      && (forall i₁₉: int ::
            (!(  old(i) <= i₁₉
              && i₁₉ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    sum := sum[0 := sum[0] + b[i]];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₂₂: int ::
            (  old(i) <= i₂₂
              && i₂₂ < i
               ==> i₂₂ < N
                && sum[0] == c[i₂₂] + old(sum)[0]))
      && (forall i₂₂: int ::
            (!(  old(i) <= i₂₂
              && i₂₂ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    sum := sum[0 := sum[0] + c[i]];
    i := i + 1;
  }
  assert sum[0] <= 3 * N;
  c#result := 1;
  return;
}

