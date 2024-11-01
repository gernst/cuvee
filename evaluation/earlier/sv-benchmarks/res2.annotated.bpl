data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  N := 0;
  havoc N;
  assume -2147483648 <= N && N < 2147483648;
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
  sum[0] := 0;
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
    a[i] := 1;
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
                && sum[0] == old(sum)[0] + a[i₁₀]))
      && (forall i₁₀: int ::
            (!(  old(i) <= i₁₀
              && i₁₀ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    sum[0] := sum[0] + a[i];
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
                && b[i₁₃] == 1))
      && (forall i₁₃: int ::
            (!(  old(i) <= i₁₃
              && i₁₃ < i
            )
               ==> b[i₁₃] == old(b)[i₁₃]));
  {
    b[i] := 1;
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
                && sum[0] == old(sum)[0] + b[i₁₆]))
      && (forall i₁₆: int ::
            (!(  old(i) <= i₁₆
              && i₁₆ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    sum[0] := sum[0] + b[i];
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
                && c[i₁₉] == 1))
      && (forall i₁₉: int ::
            (!(  old(i) <= i₁₉
              && i₁₉ < i
            )
               ==> c[i₁₉] == old(c)[i₁₉]));
  {
    c[i] := 1;
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
    sum[0] := sum[0] + c[i];
    i := i + 1;
  }
  assert sum[0] <= 3 * N;
  c#result := 1;
  return;
}

