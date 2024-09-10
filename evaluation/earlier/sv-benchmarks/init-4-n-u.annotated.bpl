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
  var l: int;
  var m: int := 1000;
  var n: int := 1500;
  var p: int := 1800;
  var q: int := 2000;
  var A: [int][int][int][int]int;
  var C: int;
  assume -2147483648 <= C && C < 2147483648;
  i := 0;
  j := 0;
  k := 0;
  l := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₂₄: int ::
            (  old(i) <= i₂₄
              && i₂₄ < i
               ==> (exists j₂₁: int ::
                      0 <= j₂₁
                      && (forall j₁₇: int ::
                            (  0 <= j₁₇
                              && j₁₇ < j₂₁
                               ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                                      0 <= k₁₄
                                      && (forall k₁₁: int ::
                                            (  0 <= k₁₁
                                              && k₁₁ < k₁₄
                                               ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                                      0 <= l₉
                                                      && (forall l₇: int ::
                                                            (  0 <= l₇
                                                              && l₇ < l₉
                                                               ==> l₇ < q
                                                                && A₈[i₂₄][j₁₇][k₁₁][l₇] == C))
                                                      && (forall l₇: int ::
                                                            (!(  0 <= l₇
                                                              && l₇ < l₉
                                                            )
                                                               ==> A₈[i₂₄][j₁₇][k₁₁][l₇] == A₁₃[i₂₄][j₁₇][k₁₁][l₇]))
                                                      && !(l₉ < q
                                                      )
                                                      && k₁₁ < p)))
                                      && !(k₁₄ < p
                                      )
                                      && j₁₇ < n)))
                      && !(j₂₁ < n
                      )
                      && i₂₄ < m)));
  {
    j := 0;
    k := 0;
    l := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₁₇: int ::
              (  old(j) <= j₁₇
                && j₁₇ < j
                 ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                        0 <= k₁₄
                        && (forall k₁₁: int ::
                              (  0 <= k₁₁
                                && k₁₁ < k₁₄
                                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                        0 <= l₉
                                        && (forall l₇: int ::
                                              (  0 <= l₇
                                                && l₇ < l₉
                                                 ==> l₇ < q
                                                  && A₈[i][j₁₇][k₁₁][l₇] == C))
                                        && (forall l₇: int ::
                                              (!(  0 <= l₇
                                                && l₇ < l₉
                                              )
                                                 ==> A₈[i][j₁₇][k₁₁][l₇] == A₁₃[i][j₁₇][k₁₁][l₇]))
                                        && !(l₉ < q
                                        )
                                        && k₁₁ < p)))
                        && !(k₁₄ < p
                        )
                        && j₁₇ < n)));
    {
      k := 0;
      l := 0;
      while(k < p)
        decreases p - k;
        invariant old(k) <= k
          && (forall k₁₁: int ::
                (  old(k) <= k₁₁
                  && k₁₁ < k
                   ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                          0 <= l₉
                          && (forall l₇: int ::
                                (  0 <= l₇
                                  && l₇ < l₉
                                   ==> l₇ < q
                                    && A₈[i][j][k₁₁][l₇] == C))
                          && (forall l₇: int ::
                                (!(  0 <= l₇
                                  && l₇ < l₉
                                )
                                   ==> A₈[i][j][k₁₁][l₇] == A[i][j][k₁₁][l₇]))
                          && !(l₉ < q
                          )
                          && k₁₁ < p)));
      {
        l := 0;
        while(l < q)
          decreases q - l;
          invariant old(l) <= l
            && (forall l₇: int ::
                  (  old(l) <= l₇
                    && l₇ < l
                     ==> l₇ < q
                      && A[i][j][k][l₇] == C))
            && (forall l₇: int ::
                  (!(  old(l) <= l₇
                    && l₇ < l
                  )
                     ==> A[i][j][k][l₇] == old(A)[i][j][k][l₇]));
        {
          A[i][j][k][l] := C;
          l := l + 1;
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
  l := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₄₆: int ::
            (  old(i) <= i₄₆
              && i₄₆ < i
               ==> (exists j₄₂: int ::
                      0 <= j₄₂
                      && (forall j₃₉: int ::
                            (  0 <= j₃₉
                              && j₃₉ < j₄₂
                               ==> (exists k₃₆: int ::
                                      0 <= k₃₆
                                      && (forall k₃₄: int ::
                                            (  0 <= k₃₄
                                              && k₃₄ < k₃₆
                                               ==> (exists l₃₂: int ::
                                                      0 <= l₃₂
                                                      && (forall l₃₁: int ::
                                                            (  0 <= l₃₁
                                                              && l₃₁ < l₃₂
                                                               ==> l₃₁ < q))
                                                      && !(l₃₂ < q
                                                      )
                                                      && k₃₄ < p)))
                                      && !(k₃₆ < p
                                      )
                                      && j₃₉ < n)))
                      && !(j₄₂ < n
                      )
                      && i₄₆ < m)));
  {
    j := 0;
    k := 0;
    l := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₃₉: int ::
              (  old(j) <= j₃₉
                && j₃₉ < j
                 ==> (exists k₃₆: int ::
                        0 <= k₃₆
                        && (forall k₃₄: int ::
                              (  0 <= k₃₄
                                && k₃₄ < k₃₆
                                 ==> (exists l₃₂: int ::
                                        0 <= l₃₂
                                        && (forall l₃₁: int ::
                                              (  0 <= l₃₁
                                                && l₃₁ < l₃₂
                                                 ==> l₃₁ < q))
                                        && !(l₃₂ < q
                                        )
                                        && k₃₄ < p)))
                        && !(k₃₆ < p
                        )
                        && j₃₉ < n)));
    {
      k := 0;
      l := 0;
      while(k < p)
        decreases p - k;
        invariant old(k) <= k
          && (forall k₃₄: int ::
                (  old(k) <= k₃₄
                  && k₃₄ < k
                   ==> (exists l₃₂: int ::
                          0 <= l₃₂
                          && (forall l₃₁: int ::
                                (  0 <= l₃₁
                                  && l₃₁ < l₃₂
                                   ==> l₃₁ < q))
                          && !(l₃₂ < q
                          )
                          && k₃₄ < p)));
      {
        l := 0;
        while(l < q)
          decreases q - l;
          invariant old(l) <= l
            && (forall l₃₁: int ::
                  (  old(l) <= l₃₁
                    && l₃₁ < l
                     ==> l₃₁ < q));
        {
          assert A[i][j][k][l] == C;
          l := l + 1;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

