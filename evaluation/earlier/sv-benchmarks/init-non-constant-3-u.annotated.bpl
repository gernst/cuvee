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
  var j: int;
  var k: int;
  var n: int := 1000;
  var A: [int][int][int]int;
  var C: int;
  assume 0 <= C && C < 4294967296;
  i := 0;
  j := 0;
  k := 0;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> (exists A₁₂: [int][int][int]int, j₁₃: int ::
                      0 <= j₁₃
                      && (forall j₁₀: int ::
                            (  0 <= j₁₀
                              && j₁₀ < j₁₃
                               ==> (exists A₇: [int][int][int]int, k₈: int ::
                                      0 <= k₈
                                      && (forall k₆: int ::
                                            (  0 <= k₆
                                              && k₆ < k₈
                                               ==> k₆ < n
                                                && A₇[i₁₆][j₁₀][k₆] == j₁₀ + k₆ + i₁₆ + C))
                                      && (forall k₆: int ::
                                            (!(  0 <= k₆
                                              && k₆ < k₈
                                            )
                                               ==> A₇[i₁₆][j₁₀][k₆] == A₁₂[i₁₆][j₁₀][k₆]))
                                      && !(k₈ < n
                                      )
                                      && j₁₀ < n)))
                      && !(j₁₃ < n
                      )
                      && i₁₆ < n)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₁₀: int ::
              (  old(j) <= j₁₀
                && j₁₀ < j
                 ==> (exists A₇: [int][int][int]int, k₈: int ::
                        0 <= k₈
                        && (forall k₆: int ::
                              (  0 <= k₆
                                && k₆ < k₈
                                 ==> k₆ < n
                                  && A₇[i][j₁₀][k₆] == j₁₀ + k₆ + i + C))
                        && (forall k₆: int ::
                              (!(  0 <= k₆
                                && k₆ < k₈
                              )
                                 ==> A₇[i][j₁₀][k₆] == A[i][j₁₀][k₆]))
                        && !(k₈ < n
                        )
                        && j₁₀ < n)));
    {
      k := 0;
      while(k < n)
        decreases n - k;
        invariant old(k) <= k
          && (forall k₆: int ::
                (  old(k) <= k₆
                  && k₆ < k
                   ==> k₆ < n
                    && A[i][j][k₆] == j + k₆ + i + C))
          && (forall k₆: int ::
                (!(  old(k) <= k₆
                  && k₆ < k
                )
                   ==> A[i][j][k₆] == old(A)[i][j][k₆]));
      {
        A[i][j][k] := i + j + k + C;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₂₉: int ::
            (  old(i) <= i₂₉
              && i₂₉ < i
               ==> (exists j₂₆: int ::
                      0 <= j₂₆
                      && (forall j₂₄: int ::
                            (  0 <= j₂₄
                              && j₂₄ < j₂₆
                               ==> (exists k₂₂: int ::
                                      0 <= k₂₂
                                      && (forall k₂₁: int ::
                                            (  0 <= k₂₁
                                              && k₂₁ < k₂₂
                                               ==> k₂₁ < n))
                                      && !(k₂₂ < n
                                      )
                                      && j₂₄ < n)))
                      && !(j₂₆ < n
                      )
                      && i₂₉ < n)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₂₄: int ::
              (  old(j) <= j₂₄
                && j₂₄ < j
                 ==> (exists k₂₂: int ::
                        0 <= k₂₂
                        && (forall k₂₁: int ::
                              (  0 <= k₂₁
                                && k₂₁ < k₂₂
                                 ==> k₂₁ < n))
                        && !(k₂₂ < n
                        )
                        && j₂₄ < n)));
    {
      k := 0;
      while(k < n)
        decreases n - k;
        invariant old(k) <= k
          && (forall k₂₁: int ::
                (  old(k) <= k₂₁
                  && k₂₁ < k
                   ==> k₂₁ < n));
      {
        assert A[i][j][k] == i + j + k + C;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

