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
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> (exists B₇: [int][int]int, j₈: int ::
                      0 <= j₈
                      && (forall j₆: int ::
                            (  0 <= j₆
                              && j₆ < j₈
                               ==> (exists nondet_int₁₅: int ::
                                      -2147483648 <= nondet_int₁₅
                                      && nondet_int₁₅ < 2147483648
                                      && j₆ < n
                                      && B₇[i₁₀][j₆] == nondet_int₁₅)))
                      && (forall j₆: int ::
                            (!(  0 <= j₆
                              && j₆ < j₈
                            )
                               ==> B₇[i₁₀][j₆] == B[i₁₀][j₆]))
                      && !(j₈ < n
                      )
                      && i₁₀ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₆: int ::
              (  old(j) <= j₆
                && j₆ < j
                 ==> (exists nondet_int₁₅: int ::
                        -2147483648 <= nondet_int₁₅
                        && nondet_int₁₅ < 2147483648
                        && j₆ < n
                        && B[i][j₆] == nondet_int₁₅)))
        && (forall j₆: int ::
              (!(  old(j) <= j₆
                && j₆ < j
              )
                 ==> B[i][j₆] == old(B)[i][j₆]));
    {
      var nondet_int₁: int;
      assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
      B[i][j] := nondet_int₁;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> (exists A₁₅: [int][int]int, j₁₆: int ::
                      0 <= j₁₆
                      && (forall j₁₄: int ::
                            (  0 <= j₁₄
                              && j₁₄ < j₁₆
                               ==> j₁₄ < n
                                && A₁₅[i₁₈][j₁₄] == B[-1 + m + -i₁₈][-1 + -j₁₄ + n]))
                      && (forall j₁₄: int ::
                            (!(  0 <= j₁₄
                              && j₁₄ < j₁₆
                            )
                               ==> A₁₅[i₁₈][j₁₄] == A[i₁₈][j₁₄]))
                      && !(j₁₆ < n
                      )
                      && i₁₈ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₁₄: int ::
              (  old(j) <= j₁₄
                && j₁₄ < j
                 ==> j₁₄ < n
                  && A[i][j₁₄] == B[-1 + -i + m][-1 + -j₁₄ + n]))
        && (forall j₁₄: int ::
              (!(  old(j) <= j₁₄
                && j₁₄ < j
              )
                 ==> A[i][j₁₄] == old(A)[i][j₁₄]));
    {
      A[i][j] := B[m - i - 1][n - j - 1];
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
               ==> (exists j₂₃: int ::
                      0 <= j₂₃
                      && (forall j₂₂: int ::
                            (  0 <= j₂₂
                              && j₂₂ < j₂₃
                               ==> j₂₂ < n))
                      && !(j₂₃ < n
                      )
                      && i₂₅ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₂₂: int ::
              (  old(j) <= j₂₂
                && j₂₂ < j
                 ==> j₂₂ < n));
    {
      assert A[i][j] == B[m - i - 1][n - j - 1];
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

