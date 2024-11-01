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
  var m: int := 1000;
  var n: int := 1500;
  var p: int := 1800;
  var A: [int][int][int]int;
  var B: [int][int][int]int;
  var C: [int][int][int]int;
  i := 0;
  j := 0;
  k := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₂₀: int ::
            (  old(i) <= i₂₀
              && i₂₀ < i
               ==> (exists A₁₆: [int][int][int]int, B₁₇: [int][int][int]int, j₁₈: int ::
                      0 <= j₁₈
                      && (forall j₁₄: int ::
                            (  0 <= j₁₄
                              && j₁₄ < j₁₈
                               ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                                      0 <= k₁₂
                                      && (forall k₉: int ::
                                            (  0 <= k₉
                                              && k₉ < k₁₂
                                               ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                                      0 <= nondet_uint₂₈
                                                      && nondet_uint₂₈ < 4294967296
                                                      && 0 <= nondet_uint₁₇
                                                      && nondet_uint₁₇ < 4294967296
                                                      && k₉ < p
                                                      && A₁₀[i₂₀][j₁₄][k₉] == nondet_uint₁₇
                                                      && B₁₁[i₂₀][j₁₄][k₉] == nondet_uint₂₈)))
                                      && (forall k₉: int ::
                                            (!(  0 <= k₉
                                              && k₉ < k₁₂
                                            )
                                               ==> A₁₀[i₂₀][j₁₄][k₉] == A₁₆[i₂₀][j₁₄][k₉]
                                                && B₁₁[i₂₀][j₁₄][k₉] == B₁₇[i₂₀][j₁₄][k₉]))
                                      && !(k₁₂ < p
                                      )
                                      && j₁₄ < n)))
                      && !(j₁₈ < n
                      )
                      && i₂₀ < m)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₁₄: int ::
              (  old(j) <= j₁₄
                && j₁₄ < j
                 ==> (exists A₁₀: [int][int][int]int, B₁₁: [int][int][int]int, k₁₂: int ::
                        0 <= k₁₂
                        && (forall k₉: int ::
                              (  0 <= k₉
                                && k₉ < k₁₂
                                 ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                                        0 <= nondet_uint₂₈
                                        && nondet_uint₂₈ < 4294967296
                                        && 0 <= nondet_uint₁₇
                                        && nondet_uint₁₇ < 4294967296
                                        && k₉ < p
                                        && A₁₀[i][j₁₄][k₉] == nondet_uint₁₇
                                        && B₁₁[i][j₁₄][k₉] == nondet_uint₂₈)))
                        && (forall k₉: int ::
                              (!(  0 <= k₉
                                && k₉ < k₁₂
                              )
                                 ==> A₁₀[i][j₁₄][k₉] == A[i][j₁₄][k₉]
                                  && B₁₁[i][j₁₄][k₉] == B[i][j₁₄][k₉]))
                        && !(k₁₂ < p
                        )
                        && j₁₄ < n)));
    {
      k := 0;
      while(k < p)
        decreases p - k;
        invariant old(k) <= k
          && (forall k₉: int ::
                (  old(k) <= k₉
                  && k₉ < k
                   ==> (exists nondet_uint₁₇: int, nondet_uint₂₈: int ::
                          0 <= nondet_uint₂₈
                          && nondet_uint₂₈ < 4294967296
                          && 0 <= nondet_uint₁₇
                          && nondet_uint₁₇ < 4294967296
                          && k₉ < p
                          && A[i][j][k₉] == nondet_uint₁₇
                          && B[i][j][k₉] == nondet_uint₂₈)))
          && (forall k₉: int ::
                (!(  old(k) <= k₉
                  && k₉ < k
                )
                   ==> A[i][j][k₉] == old(A)[i][j][k₉]
                    && B[i][j][k₉] == old(B)[i][j][k₉]));
      {
        var nondet_uint₁: int;
        assume 0 <= nondet_uint₁ && nondet_uint₁ < 4294967296;
        A[i][j][k] := nondet_uint₁;
        var nondet_uint₂: int;
        assume 0 <= nondet_uint₂ && nondet_uint₂ < 4294967296;
        B[i][j][k] := nondet_uint₂;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₃₇: int ::
            (  old(i) <= i₃₇
              && i₃₇ < i
               ==> (exists C₃₃: [int][int][int]int, j₃₄: int ::
                      0 <= j₃₄
                      && (forall j₃₁: int ::
                            (  0 <= j₃₁
                              && j₃₁ < j₃₄
                               ==> (exists C₂₈: [int][int][int]int, k₂₉: int ::
                                      0 <= k₂₉
                                      && (forall k₂₇: int ::
                                            (  0 <= k₂₇
                                              && k₂₇ < k₂₉
                                               ==> k₂₇ < p
                                                && C₂₈[i₃₇][j₃₁][k₂₇] == B[i₃₇][j₃₁][k₂₇] + A[i₃₇][j₃₁][k₂₇]))
                                      && (forall k₂₇: int ::
                                            (!(  0 <= k₂₇
                                              && k₂₇ < k₂₉
                                            )
                                               ==> C₂₈[i₃₇][j₃₁][k₂₇] == C₃₃[i₃₇][j₃₁][k₂₇]))
                                      && !(k₂₉ < p
                                      )
                                      && j₃₁ < n)))
                      && !(j₃₄ < n
                      )
                      && i₃₇ < m)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₃₁: int ::
              (  old(j) <= j₃₁
                && j₃₁ < j
                 ==> (exists C₂₈: [int][int][int]int, k₂₉: int ::
                        0 <= k₂₉
                        && (forall k₂₇: int ::
                              (  0 <= k₂₇
                                && k₂₇ < k₂₉
                                 ==> k₂₇ < p
                                  && C₂₈[i][j₃₁][k₂₇] == B[i][j₃₁][k₂₇] + A[i][j₃₁][k₂₇]))
                        && (forall k₂₇: int ::
                              (!(  0 <= k₂₇
                                && k₂₇ < k₂₉
                              )
                                 ==> C₂₈[i][j₃₁][k₂₇] == C[i][j₃₁][k₂₇]))
                        && !(k₂₉ < p
                        )
                        && j₃₁ < n)));
    {
      k := 0;
      while(k < p)
        decreases p - k;
        invariant old(k) <= k
          && (forall k₂₇: int ::
                (  old(k) <= k₂₇
                  && k₂₇ < k
                   ==> k₂₇ < p
                    && C[i][j][k₂₇] == B[i][j][k₂₇] + A[i][j][k₂₇]))
          && (forall k₂₇: int ::
                (!(  old(k) <= k₂₇
                  && k₂₇ < k
                )
                   ==> C[i][j][k₂₇] == old(C)[i][j][k₂₇]));
      {
        C[i][j][k] := A[i][j][k] + B[i][j][k];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₅₀: int ::
            (  old(i) <= i₅₀
              && i₅₀ < i
               ==> (exists j₄₇: int ::
                      0 <= j₄₇
                      && (forall j₄₅: int ::
                            (  0 <= j₄₅
                              && j₄₅ < j₄₇
                               ==> (exists k₄₃: int ::
                                      0 <= k₄₃
                                      && (forall k₄₂: int ::
                                            (  0 <= k₄₂
                                              && k₄₂ < k₄₃
                                               ==> k₄₂ < p))
                                      && !(k₄₃ < p
                                      )
                                      && j₄₅ < n)))
                      && !(j₄₇ < n
                      )
                      && i₅₀ < m)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₄₅: int ::
              (  old(j) <= j₄₅
                && j₄₅ < j
                 ==> (exists k₄₃: int ::
                        0 <= k₄₃
                        && (forall k₄₂: int ::
                              (  0 <= k₄₂
                                && k₄₂ < k₄₃
                                 ==> k₄₂ < p))
                        && !(k₄₃ < p
                        )
                        && j₄₅ < n)));
    {
      k := 0;
      while(k < p)
        decreases p - k;
        invariant old(k) <= k
          && (forall k₄₂: int ::
                (  old(k) <= k₄₂
                  && k₄₂ < k
                   ==> k₄₂ < p));
      {
        assert C[i][j][k] == A[i][j][k] + B[i][j][k];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

