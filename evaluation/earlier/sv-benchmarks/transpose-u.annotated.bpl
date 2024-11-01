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
  var k: int;
  var j: int;
  var n: int := 1000;
  var A: [int][int]int;
  var C: [int][int]int;
  i := 0;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> (exists A₈: [int][int]int, j₉: int ::
                      0 <= j₉
                      && (forall j₇: int ::
                            (  0 <= j₇
                              && j₇ < j₉
                               ==> (exists nondet_int₁₆: int ::
                                      -2147483648 <= nondet_int₁₆
                                      && nondet_int₁₆ < 2147483648
                                      && j₇ < n
                                      && A₈[i₁₁][j₇] == nondet_int₁₆)))
                      && (forall j₇: int ::
                            (!(  0 <= j₇
                              && j₇ < j₉
                            )
                               ==> A₈[i₁₁][j₇] == A[i₁₁][j₇]))
                      && !(j₉ < n
                      )
                      && i₁₁ < n)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₇: int ::
              (  old(j) <= j₇
                && j₇ < j
                 ==> (exists nondet_int₁₆: int ::
                        -2147483648 <= nondet_int₁₆
                        && nondet_int₁₆ < 2147483648
                        && j₇ < n
                        && A[i][j₇] == nondet_int₁₆)))
        && (forall j₇: int ::
              (!(  old(j) <= j₇
                && j₇ < j
              )
                 ==> A[i][j₇] == old(A)[i][j₇]));
    {
      var nondet_int₁: int;
      assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
      A[i][j] := nondet_int₁;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₁₉: int ::
            (  old(i) <= i₁₉
              && i₁₉ < i
               ==> (exists C₁₆: [int][int]int, j₁₇: int ::
                      0 <= j₁₇
                      && (forall j₁₅: int ::
                            (  0 <= j₁₅
                              && j₁₅ < j₁₇
                               ==> j₁₅ < n
                                && C₁₆[j₁₅][i₁₉] == A[i₁₉][j₁₅]))
                      && (forall j₁₅: int ::
                            (!(  0 <= j₁₅
                              && j₁₅ < j₁₇
                            )
                               ==> C₁₆[j₁₅][i₁₉] == C[j₁₅][i₁₉]))
                      && !(j₁₇ < n
                      )
                      && i₁₉ < n)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₁₅: int ::
              (  old(j) <= j₁₅
                && j₁₅ < j
                 ==> j₁₅ < n
                  && C[j₁₅][i] == A[i][j₁₅]))
        && (forall j₁₅: int ::
              (!(  old(j) <= j₁₅
                && j₁₅ < j
              )
                 ==> C[j₁₅][i] == old(C)[j₁₅][i]));
    {
      C[j][i] := A[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₂₆: int ::
            (  old(i) <= i₂₆
              && i₂₆ < i
               ==> (exists j₂₄: int ::
                      0 <= j₂₄
                      && (forall j₂₃: int ::
                            (  0 <= j₂₃
                              && j₂₃ < j₂₄
                               ==> j₂₃ < n))
                      && !(j₂₄ < n
                      )
                      && i₂₆ < n)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₂₃: int ::
              (  old(j) <= j₂₃
                && j₂₃ < j
                 ==> j₂₃ < n));
    {
      assert C[j][i] == A[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

