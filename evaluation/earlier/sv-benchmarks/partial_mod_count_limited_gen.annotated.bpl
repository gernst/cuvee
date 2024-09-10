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
  N := 1000;
  var i: int;
  var j: int := 0;
  var k: int := 0;
  var a: [int]int;
  var lim: int;
  assume -2147483648 <= lim && lim < 2147483648;
  var R: int;
  assume 0 <= R && R < 4294967296;
  assume 1 < R && R < 6;
  assume 0 < lim && lim < N / R;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(k) + k == i + old(i)
      && old(k) <= k
      && old(i) <= i
      && (forall k₅: int, i₆: int ::
            (  k₅ + old(k₅) == old(i₆) + i₆
              && old(k) <= k₅
              && k₅ < k
              && old(i) <= i₆
              && i₆ < i
               ==> i₆ % R == 0
                  && N / R < i₆
                  && k₅ < lim
                  && i₆ < N
                  && a[i₆] == i₆ % R
                ||   1 + i₆ == 0
                  && !(  N / R < i₆
                    && k₅ < lim
                  )
                  && i₆ < N
                  && a[i₆] == 1 + i₆
                ||   i₆ % R != 0
                  && N / R < i₆
                  && k₅ < lim
                  && i₆ < N
                  && a[i₆] == i₆ % R
                ||   1 + i₆ != 0
                  && !(  N / R < i₆
                    && k₅ < lim
                  )
                  && i₆ < N
                  && a[i₆] == 1 + i₆))
      && (forall k₅: int, i₆: int ::
            (  k₅ + old(k₅) == old(i₆) + i₆
              && !(  old(k) <= k₅
                && k₅ < k
                && old(i) <= i₆
                && i₆ < i
              )
               ==> a[i₆] == old(a)[i₆]));
  {
    a[i] := i + 1;
    if(N / R < i && k < lim) {
      a[i] := i % R;
    }
    if(a[i] == 0) {
      k := k + 1;
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant j + old(j) == i + old(i)
      && old(j) <= j
      && old(i) <= i
      && (forall j₁₀: int, i₁₁: int ::
            (  j₁₀ + old(j₁₀) == i₁₁ + old(i₁₁)
              && old(j) <= j₁₀
              && j₁₀ < j
              && old(i) <= i₁₁
              && i₁₁ < i
               ==> a[i₁₁] == 0
                  && i₁₁ < N
                ||   a[i₁₁] != 0
                  && i₁₁ < N));
  {
    if(a[i] == 0) {
      j := j + 1;
    }
    assert j <= N * (R - 1) / R * R;
    i := i + 1;
  }
  c#result := 0;
  return;
}

