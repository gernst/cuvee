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
  var m: int := 1000;
  var n: int := 1500;
  var A: [int][int]int;
  var B: [int][int]int;
  var C: [int][int]int;
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> (exists A₉: [int][int]int, B₁₀: [int][int]int, j₁₁: int ::
                      0 <= j₁₁
                      && (forall j₈: int ::
                            (  0 <= j₈
                              && j₈ < j₁₁
                               ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                                      0 <= nondet_uint₂₇
                                      && nondet_uint₂₇ < 4294967296
                                      && 0 <= nondet_uint₁₆
                                      && nondet_uint₁₆ < 4294967296
                                      && j₈ < n
                                      && A₉[i₁₃][j₈] == nondet_uint₁₆
                                      && B₁₀[i₁₃][j₈] == nondet_uint₂₇)))
                      && (forall j₈: int ::
                            (!(  0 <= j₈
                              && j₈ < j₁₁
                            )
                               ==> A₉[i₁₃][j₈] == A[i₁₃][j₈]
                                && B₁₀[i₁₃][j₈] == B[i₁₃][j₈]))
                      && !(j₁₁ < n
                      )
                      && i₁₃ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₈: int ::
              (  old(j) <= j₈
                && j₈ < j
                 ==> (exists nondet_uint₁₆: int, nondet_uint₂₇: int ::
                        0 <= nondet_uint₂₇
                        && nondet_uint₂₇ < 4294967296
                        && 0 <= nondet_uint₁₆
                        && nondet_uint₁₆ < 4294967296
                        && j₈ < n
                        && A[i][j₈] == nondet_uint₁₆
                        && B[i][j₈] == nondet_uint₂₇)))
        && (forall j₈: int ::
              (!(  old(j) <= j₈
                && j₈ < j
              )
                 ==> A[i][j₈] == old(A)[i][j₈]
                  && B[i][j₈] == old(B)[i][j₈]));
    {
      var nondet_uint₁: int;
      assume 0 <= nondet_uint₁ && nondet_uint₁ < 4294967296;
      A[i][j] := nondet_uint₁;
      var nondet_uint₂: int;
      assume 0 <= nondet_uint₂ && nondet_uint₂ < 4294967296;
      B[i][j] := nondet_uint₂;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₂₅: int ::
            (  old(i) <= i₂₅
              && i₂₅ < i
               ==> (exists A₂₁: [int][int]int, B₂₂: [int][int]int, j₂₃: int ::
                      0 <= j₂₃
                      && (forall j₂₀: int ::
                            (  0 <= j₂₀
                              && j₂₀ < j₂₃
                               ==> (exists nondet_uint₃₁₈: int, nondet_uint₄₁₉: int ::
                                      0 <= nondet_uint₄₁₉
                                      && nondet_uint₄₁₉ < 4294967296
                                      && 0 <= nondet_uint₃₁₈
                                      && nondet_uint₃₁₈ < 4294967296
                                      && j₂₀ < n
                                      && A₂₁[i₂₅][j₂₀] == nondet_uint₃₁₈
                                      && B₂₂[i₂₅][j₂₀] == nondet_uint₄₁₉)))
                      && (forall j₂₀: int ::
                            (!(  0 <= j₂₀
                              && j₂₀ < j₂₃
                            )
                               ==> A₂₁[i₂₅][j₂₀] == A[i₂₅][j₂₀]
                                && B₂₂[i₂₅][j₂₀] == B[i₂₅][j₂₀]))
                      && !(j₂₃ < n
                      )
                      && i₂₅ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₂₀: int ::
              (  old(j) <= j₂₀
                && j₂₀ < j
                 ==> (exists nondet_uint₃₁₈: int, nondet_uint₄₁₉: int ::
                        0 <= nondet_uint₄₁₉
                        && nondet_uint₄₁₉ < 4294967296
                        && 0 <= nondet_uint₃₁₈
                        && nondet_uint₃₁₈ < 4294967296
                        && j₂₀ < n
                        && A[i][j₂₀] == nondet_uint₃₁₈
                        && B[i][j₂₀] == nondet_uint₄₁₉)))
        && (forall j₂₀: int ::
              (!(  old(j) <= j₂₀
                && j₂₀ < j
              )
                 ==> A[i][j₂₀] == old(A)[i][j₂₀]
                  && B[i][j₂₀] == old(B)[i][j₂₀]));
    {
      var nondet_uint₃: int;
      assume 0 <= nondet_uint₃ && nondet_uint₃ < 4294967296;
      A[i][j] := nondet_uint₃;
      var nondet_uint₄: int;
      assume 0 <= nondet_uint₄ && nondet_uint₄ < 4294967296;
      B[i][j] := nondet_uint₄;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₃₄: int ::
            (  old(i) <= i₃₄
              && i₃₄ < i
               ==> (exists C₃₁: [int][int]int, j₃₂: int ::
                      0 <= j₃₂
                      && (forall j₃₀: int ::
                            (  0 <= j₃₀
                              && j₃₀ < j₃₂
                               ==> j₃₀ < n
                                && C₃₁[i₃₄][j₃₀] == A[i₃₄][j₃₀] + -B[i₃₄][j₃₀]))
                      && (forall j₃₀: int ::
                            (!(  0 <= j₃₀
                              && j₃₀ < j₃₂
                            )
                               ==> C₃₁[i₃₄][j₃₀] == C[i₃₄][j₃₀]))
                      && !(j₃₂ < n
                      )
                      && i₃₄ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₃₀: int ::
              (  old(j) <= j₃₀
                && j₃₀ < j
                 ==> j₃₀ < n
                  && C[i][j₃₀] == -B[i][j₃₀] + A[i][j₃₀]))
        && (forall j₃₀: int ::
              (!(  old(j) <= j₃₀
                && j₃₀ < j
              )
                 ==> C[i][j₃₀] == old(C)[i][j₃₀]));
    {
      C[i][j] := A[i][j] - B[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₄₁: int ::
            (  old(i) <= i₄₁
              && i₄₁ < i
               ==> (exists j₃₉: int ::
                      0 <= j₃₉
                      && (forall j₃₈: int ::
                            (  0 <= j₃₈
                              && j₃₈ < j₃₉
                               ==> j₃₈ < n))
                      && !(j₃₉ < n
                      )
                      && i₄₁ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₃₈: int ::
              (  old(j) <= j₃₈
                && j₃₈ < j
                 ==> j₃₈ < n));
    {
      assert C[i][j] == A[i][j] - B[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

