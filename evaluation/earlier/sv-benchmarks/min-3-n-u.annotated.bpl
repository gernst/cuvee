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
  var min: int;
  i := 0;
  j := 0;
  k := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> (exists A₁₃: [int][int][int]int, j₁₄: int ::
                      0 <= j₁₄
                      && (forall j₁₁: int ::
                            (  0 <= j₁₁
                              && j₁₁ < j₁₄
                               ==> (exists A₈: [int][int][int]int, k₉: int ::
                                      0 <= k₉
                                      && (forall k₇: int ::
                                            (  0 <= k₇
                                              && k₇ < k₉
                                               ==> (exists nondet_int₁₆: int ::
                                                      -2147483648 <= nondet_int₁₆
                                                      && nondet_int₁₆ < 2147483648
                                                      && k₇ < p
                                                      && A₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                      && (forall k₇: int ::
                                            (!(  0 <= k₇
                                              && k₇ < k₉
                                            )
                                               ==> A₈[i₁₇][j₁₁][k₇] == A₁₃[i₁₇][j₁₁][k₇]))
                                      && !(k₉ < p
                                      )
                                      && j₁₁ < n)))
                      && !(j₁₄ < n
                      )
                      && i₁₇ < m)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₁₁: int ::
              (  old(j) <= j₁₁
                && j₁₁ < j
                 ==> (exists A₈: [int][int][int]int, k₉: int ::
                        0 <= k₉
                        && (forall k₇: int ::
                              (  0 <= k₇
                                && k₇ < k₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && k₇ < p
                                        && A₈[i][j₁₁][k₇] == nondet_int₁₆)))
                        && (forall k₇: int ::
                              (!(  0 <= k₇
                                && k₇ < k₉
                              )
                                 ==> A₈[i][j₁₁][k₇] == A[i][j₁₁][k₇]))
                        && !(k₉ < p
                        )
                        && j₁₁ < n)));
    {
      k := 0;
      while(k < p)
        decreases p - k;
        invariant old(k) <= k
          && (forall k₇: int ::
                (  old(k) <= k₇
                  && k₇ < k
                   ==> (exists nondet_int₁₆: int ::
                          -2147483648 <= nondet_int₁₆
                          && nondet_int₁₆ < 2147483648
                          && k₇ < p
                          && A[i][j][k₇] == nondet_int₁₆)))
          && (forall k₇: int ::
                (!(  old(k) <= k₇
                  && k₇ < k
                )
                   ==> A[i][j][k₇] == old(A)[i][j][k₇]));
      {
        var nondet_int₁: int;
        assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
        A[i][j][k] := nondet_int₁;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  min := A[0][0][0];
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₃₅: int ::
            (  old(i) <= i₃₅
              && i₃₅ < i
               ==> (exists j₃₁: int ::
                      0 <= j₃₁
                      && (forall j₂₈: int ::
                            (  0 <= j₂₈
                              && j₂₈ < j₃₁
                               ==> (exists k₂₅: int ::
                                      0 <= k₂₅
                                      && (forall min₂₂: int, k₂₃: int ::
                                            (  0 <= k₂₃
                                              && k₂₃ < k₂₅
                                               ==> A[i₃₅][j₂₈][k₂₃] < min₂₂
                                                  && k₂₃ < p
                                                ||   !(A[i₃₅][j₂₈][k₂₃] < min₂₂
                                                  )
                                                  && k₂₃ < p))
                                      && !(k₂₅ < p
                                      )
                                      && j₂₈ < n)))
                      && !(j₃₁ < n
                      )
                      && i₃₅ < m)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₂₈: int ::
              (  old(j) <= j₂₈
                && j₂₈ < j
                 ==> (exists k₂₅: int ::
                        0 <= k₂₅
                        && (forall min₂₂: int, k₂₃: int ::
                              (  0 <= k₂₃
                                && k₂₃ < k₂₅
                                 ==> A[i][j₂₈][k₂₃] < min₂₂
                                    && k₂₃ < p
                                  ||   !(A[i][j₂₈][k₂₃] < min₂₂
                                    )
                                    && k₂₃ < p))
                        && !(k₂₅ < p
                        )
                        && j₂₈ < n)));
    {
      k := 0;
      while(k < p)
        decreases p - k;
        invariant old(k) <= k
          && (forall min₂₂: int, k₂₃: int ::
                (  old(k) <= k₂₃
                  && k₂₃ < k
                   ==> A[i][j][k₂₃] < min₂₂
                      && k₂₃ < p
                    ||   !(A[i][j][k₂₃] < min₂₂
                      )
                      && k₂₃ < p));
      {
        if(A[i][j][k] < min) {
          min := A[i][j][k];
        }
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
      && (forall i₄₈: int ::
            (  old(i) <= i₄₈
              && i₄₈ < i
               ==> (exists j₄₅: int ::
                      0 <= j₄₅
                      && (forall j₄₃: int ::
                            (  0 <= j₄₃
                              && j₄₃ < j₄₅
                               ==> (exists k₄₁: int ::
                                      0 <= k₄₁
                                      && (forall k₄₀: int ::
                                            (  0 <= k₄₀
                                              && k₄₀ < k₄₁
                                               ==> k₄₀ < p))
                                      && !(k₄₁ < p
                                      )
                                      && j₄₃ < n)))
                      && !(j₄₅ < n
                      )
                      && i₄₈ < m)));
  {
    j := 0;
    k := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₄₃: int ::
              (  old(j) <= j₄₃
                && j₄₃ < j
                 ==> (exists k₄₁: int ::
                        0 <= k₄₁
                        && (forall k₄₀: int ::
                              (  0 <= k₄₀
                                && k₄₀ < k₄₁
                                 ==> k₄₀ < p))
                        && !(k₄₁ < p
                        )
                        && j₄₃ < n)));
    {
      k := 0;
      while(k < p)
        decreases p - k;
        invariant old(k) <= k
          && (forall k₄₀: int ::
                (  old(k) <= k₄₀
                  && k₄₀ < k
                   ==> k₄₀ < p));
      {
        assert min <= A[i][j][k];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

