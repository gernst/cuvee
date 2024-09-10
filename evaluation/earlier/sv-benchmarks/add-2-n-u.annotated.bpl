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
      && (forall i₂₂: int ::
            (  old(i) <= i₂₂
              && i₂₂ < i
               ==> (exists C₁₉: [int][int]int, j₂₀: int ::
                      0 <= j₂₀
                      && (forall j₁₈: int ::
                            (  0 <= j₁₈
                              && j₁₈ < j₂₀
                               ==> j₁₈ < n
                                && C₁₉[i₂₂][j₁₈] == B[i₂₂][j₁₈] + A[i₂₂][j₁₈]))
                      && (forall j₁₈: int ::
                            (!(  0 <= j₁₈
                              && j₁₈ < j₂₀
                            )
                               ==> C₁₉[i₂₂][j₁₈] == C[i₂₂][j₁₈]))
                      && !(j₂₀ < n
                      )
                      && i₂₂ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₁₈: int ::
              (  old(j) <= j₁₈
                && j₁₈ < j
                 ==> j₁₈ < n
                  && C[i][j₁₈] == B[i][j₁₈] + A[i][j₁₈]))
        && (forall j₁₈: int ::
              (!(  old(j) <= j₁₈
                && j₁₈ < j
              )
                 ==> C[i][j₁₈] == old(C)[i][j₁₈]));
    {
      C[i][j] := A[i][j] + B[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₂₉: int ::
            (  old(i) <= i₂₉
              && i₂₉ < i
               ==> (exists j₂₇: int ::
                      0 <= j₂₇
                      && (forall j₂₆: int ::
                            (  0 <= j₂₆
                              && j₂₆ < j₂₇
                               ==> j₂₆ < n))
                      && !(j₂₇ < n
                      )
                      && i₂₉ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₂₆: int ::
              (  old(j) <= j₂₆
                && j₂₆ < j
                 ==> j₂₆ < n));
    {
      assert C[i][j] == A[i][j] + B[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

