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
  var p: int := 500;
  var A: [int][int][int]int;
  var B: [int][int][int]int;
  assume p < n;
  i := 0;
  j := 0;
  k := 0;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> (exists B₁₃: [int][int][int]int, j₁₄: int ::
                      0 <= j₁₄
                      && (forall j₁₁: int ::
                            (  0 <= j₁₁
                              && j₁₁ < j₁₄
                               ==> (exists B₈: [int][int][int]int, k₉: int ::
                                      0 <= k₉
                                      && (forall k₇: int ::
                                            (  0 <= k₇
                                              && k₇ < k₉
                                               ==> (exists nondet_int₁₆: int ::
                                                      -2147483648 <= nondet_int₁₆
                                                      && nondet_int₁₆ < 2147483648
                                                      && k₇ < n
                                                      && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                      && (forall k₇: int ::
                                            (!(  0 <= k₇
                                              && k₇ < k₉
                                            )
                                               ==> B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇]))
                                      && !(k₉ < n
                                      )
                                      && j₁₁ < n)))
                      && !(j₁₄ < n
                      )
                      && i₁₇ < n)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₁₁: int ::
              (  old(j) <= j₁₁
                && j₁₁ < j
                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                        0 <= k₉
                        && (forall k₇: int ::
                              (  0 <= k₇
                                && k₇ < k₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && k₇ < n
                                        && B₈[i][j₁₁][k₇] == nondet_int₁₆)))
                        && (forall k₇: int ::
                              (!(  0 <= k₇
                                && k₇ < k₉
                              )
                                 ==> B₈[i][j₁₁][k₇] == B[i][j₁₁][k₇]))
                        && !(k₉ < n
                        )
                        && j₁₁ < n)));
    {
      k := 0;
      while(k < n)
        decreases n - k;
        invariant old(k) <= k
          && (forall k₇: int ::
                (  old(k) <= k₇
                  && k₇ < k
                   ==> (exists nondet_int₁₆: int ::
                          -2147483648 <= nondet_int₁₆
                          && nondet_int₁₆ < 2147483648
                          && k₇ < n
                          && B[i][j][k₇] == nondet_int₁₆)))
          && (forall k₇: int ::
                (!(  old(k) <= k₇
                  && k₇ < k
                )
                   ==> B[i][j][k₇] == old(B)[i][j][k₇]));
      {
        var nondet_int₁: int;
        assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
        B[i][j][k] := nondet_int₁;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while(i < p)
    decreases p - i;
    invariant old(i) <= i
      && (forall i₃₂: int ::
            (  old(i) <= i₃₂
              && i₃₂ < i
               ==> (exists A₂₈: [int][int][int]int, j₂₉: int ::
                      0 <= j₂₉
                      && (forall j₂₆: int ::
                            (  0 <= j₂₆
                              && j₂₆ < j₂₉
                               ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                                      0 <= k₂₄
                                      && (forall k₂₂: int ::
                                            (  0 <= k₂₂
                                              && k₂₂ < k₂₄
                                               ==> k₂₂ < p
                                                && A₂₃[i₃₂][j₂₆][k₂₂] == B[i₃₂][j₂₆][k₂₂]))
                                      && (forall k₂₂: int ::
                                            (!(  0 <= k₂₂
                                              && k₂₂ < k₂₄
                                            )
                                               ==> A₂₃[i₃₂][j₂₆][k₂₂] == A₂₈[i₃₂][j₂₆][k₂₂]))
                                      && !(k₂₄ < p
                                      )
                                      && j₂₆ < p)))
                      && !(j₂₉ < p
                      )
                      && i₃₂ < p)));
  {
    j := 0;
    k := 0;
    while(j < p)
      decreases p - j;
      invariant old(j) <= j
        && (forall j₂₆: int ::
              (  old(j) <= j₂₆
                && j₂₆ < j
                 ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                        0 <= k₂₄
                        && (forall k₂₂: int ::
                              (  0 <= k₂₂
                                && k₂₂ < k₂₄
                                 ==> k₂₂ < p
                                  && A₂₃[i][j₂₆][k₂₂] == B[i][j₂₆][k₂₂]))
                        && (forall k₂₂: int ::
                              (!(  0 <= k₂₂
                                && k₂₂ < k₂₄
                              )
                                 ==> A₂₃[i][j₂₆][k₂₂] == A[i][j₂₆][k₂₂]))
                        && !(k₂₄ < p
                        )
                        && j₂₆ < p)));
    {
      k := 0;
      while(k < p)
        decreases p - k;
        invariant old(k) <= k
          && (forall k₂₂: int ::
                (  old(k) <= k₂₂
                  && k₂₂ < k
                   ==> k₂₂ < p
                    && A[i][j][k₂₂] == B[i][j][k₂₂]))
          && (forall k₂₂: int ::
                (!(  old(k) <= k₂₂
                  && k₂₂ < k
                )
                   ==> A[i][j][k₂₂] == old(A)[i][j][k₂₂]));
      {
        A[i][j][k] := B[i][j][k];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := p;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₄₇: int ::
            (  old(i) <= i₄₇
              && i₄₇ < i
               ==> (exists A₄₃: [int][int][int]int, j₄₄: int ::
                      p <= j₄₄
                      && (forall j₄₁: int ::
                            (  p <= j₄₁
                              && j₄₁ < j₄₄
                               ==> (exists A₃₈: [int][int][int]int, k₃₉: int ::
                                      p <= k₃₉
                                      && (forall k₃₇: int ::
                                            (  p <= k₃₇
                                              && k₃₇ < k₃₉
                                               ==> k₃₇ < n
                                                && A₃₈[i₄₇][j₄₁][k₃₇] == B[i₄₇][j₄₁][k₃₇]))
                                      && (forall k₃₇: int ::
                                            (!(  p <= k₃₇
                                              && k₃₇ < k₃₉
                                            )
                                               ==> A₃₈[i₄₇][j₄₁][k₃₇] == A₄₃[i₄₇][j₄₁][k₃₇]))
                                      && !(k₃₉ < n
                                      )
                                      && j₄₁ < n)))
                      && !(j₄₄ < n
                      )
                      && i₄₇ < n)));
  {
    j := p;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₄₁: int ::
              (  old(j) <= j₄₁
                && j₄₁ < j
                 ==> (exists A₃₈: [int][int][int]int, k₃₉: int ::
                        p <= k₃₉
                        && (forall k₃₇: int ::
                              (  p <= k₃₇
                                && k₃₇ < k₃₉
                                 ==> k₃₇ < n
                                  && A₃₈[i][j₄₁][k₃₇] == B[i][j₄₁][k₃₇]))
                        && (forall k₃₇: int ::
                              (!(  p <= k₃₇
                                && k₃₇ < k₃₉
                              )
                                 ==> A₃₈[i][j₄₁][k₃₇] == A[i][j₄₁][k₃₇]))
                        && !(k₃₉ < n
                        )
                        && j₄₁ < n)));
    {
      k := p;
      while(k < n)
        decreases n - k;
        invariant old(k) <= k
          && (forall k₃₇: int ::
                (  old(k) <= k₃₇
                  && k₃₇ < k
                   ==> k₃₇ < n
                    && A[i][j][k₃₇] == B[i][j][k₃₇]))
          && (forall k₃₇: int ::
                (!(  old(k) <= k₃₇
                  && k₃₇ < k
                )
                   ==> A[i][j][k₃₇] == old(A)[i][j][k₃₇]));
      {
        A[i][j][k] := B[i][j][k];
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
      && (forall i₆₀: int ::
            (  old(i) <= i₆₀
              && i₆₀ < i
               ==> (exists j₅₇: int ::
                      0 <= j₅₇
                      && (forall j₅₅: int ::
                            (  0 <= j₅₅
                              && j₅₅ < j₅₇
                               ==> (exists k₅₃: int ::
                                      0 <= k₅₃
                                      && (forall k₅₂: int ::
                                            (  0 <= k₅₂
                                              && k₅₂ < k₅₃
                                               ==> k₅₂ < n))
                                      && !(k₅₃ < n
                                      )
                                      && j₅₅ < n)))
                      && !(j₅₇ < n
                      )
                      && i₆₀ < n)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₅₅: int ::
              (  old(j) <= j₅₅
                && j₅₅ < j
                 ==> (exists k₅₃: int ::
                        0 <= k₅₃
                        && (forall k₅₂: int ::
                              (  0 <= k₅₂
                                && k₅₂ < k₅₃
                                 ==> k₅₂ < n))
                        && !(k₅₃ < n
                        )
                        && j₅₅ < n)));
    {
      k := 0;
      while(k < n)
        decreases n - k;
        invariant old(k) <= k
          && (forall k₅₂: int ::
                (  old(k) <= k₅₂
                  && k₅₂ < k
                   ==> k₅₂ < n));
      {
        assert A[i][j][k] == B[i][j][k];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

