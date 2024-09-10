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
  var R: int := 3;
  assume 0 < lim && lim < N / R;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(k) + k == i + old(i)
      && old(k) <= k
      && old(i) <= i
      && (forall k₄: int, i₅: int ::
            (  k₄ + old(k₄) == i₅ + old(i₅)
              && old(k) <= k₄
              && k₄ < k
              && old(i) <= i₅
              && i₅ < i
               ==> i₅ % R == 0
                  && N / 2 < i₅
                  && k₄ < lim
                  && i₅ < N
                  && a[i₅] == i₅ % R
                ||   1 + i₅ == 0
                  && !(  N / 2 < i₅
                    && k₄ < lim
                  )
                  && i₅ < N
                  && a[i₅] == 1 + i₅
                ||   i₅ % R != 0
                  && N / 2 < i₅
                  && k₄ < lim
                  && i₅ < N
                  && a[i₅] == i₅ % R
                ||   1 + i₅ != 0
                  && !(  N / 2 < i₅
                    && k₄ < lim
                  )
                  && i₅ < N
                  && a[i₅] == 1 + i₅))
      && (forall k₄: int, i₅: int ::
            (  k₄ + old(k₄) == i₅ + old(i₅)
              && !(  old(k) <= k₄
                && k₄ < k
                && old(i) <= i₅
                && i₅ < i
              )
               ==> a[i₅] == old(a)[i₅]));
  {
    a[i] := i + 1;
    if(N / 2 < i && k < lim) {
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
      && (forall j₉: int, i₁₀: int ::
            (  j₉ + old(j₉) == old(i₁₀) + i₁₀
              && old(j) <= j₉
              && j₉ < j
              && old(i) <= i₁₀
              && i₁₀ < i
               ==> a[i₁₀] == 0
                  && i₁₀ < N
                ||   a[i₁₀] != 0
                  && i₁₀ < N));
  {
    if(a[i] == 0) {
      j := j + 1;
    }
    assert j < N / 2 * R + 2;
    i := i + 1;
  }
  c#result := 0;
  return;
}

