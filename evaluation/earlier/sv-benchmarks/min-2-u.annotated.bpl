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
  var min: int;
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₁₀: int ::
            (  old(i) <= i₁₀
              && i₁₀ < i
               ==> (exists A₇: [int][int]int, j₈: int ::
                      0 <= j₈
                      && (forall j₆: int ::
                            (  0 <= j₆
                              && j₆ < j₈
                               ==> (exists nondet_int₁₅: int ::
                                      -2147483648 <= nondet_int₁₅
                                      && nondet_int₁₅ < 2147483648
                                      && j₆ < n
                                      && A₇[i₁₀][j₆] == nondet_int₁₅)))
                      && (forall j₆: int ::
                            (!(  0 <= j₆
                              && j₆ < j₈
                            )
                               ==> A₇[i₁₀][j₆] == A[i₁₀][j₆]))
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
                        && A[i][j₆] == nondet_int₁₅)))
        && (forall j₆: int ::
              (!(  old(j) <= j₆
                && j₆ < j
              )
                 ==> A[i][j₆] == old(A)[i][j₆]));
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
  min := A[0][0];
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₂₀: int ::
            (  old(i) <= i₂₀
              && i₂₀ < i
               ==> (exists j₁₇: int ::
                      0 <= j₁₇
                      && (forall min₁₄: int, j₁₅: int ::
                            (  0 <= j₁₅
                              && j₁₅ < j₁₇
                               ==> A[i₂₀][j₁₅] < min₁₄
                                  && j₁₅ < n
                                ||   !(A[i₂₀][j₁₅] < min₁₄
                                  )
                                  && j₁₅ < n))
                      && !(j₁₇ < n
                      )
                      && i₂₀ < n)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall min₁₄: int, j₁₅: int ::
              (  old(j) <= j₁₅
                && j₁₅ < j
                 ==> A[i][j₁₅] < min₁₄
                    && j₁₅ < n
                  ||   !(A[i][j₁₅] < min₁₄
                    )
                    && j₁₅ < n));
    {
      if(A[i][j] < min) {
        min := A[i][j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < n)
    decreases n - i;
    invariant old(i) <= i
      && (forall i₂₇: int ::
            (  old(i) <= i₂₇
              && i₂₇ < i
               ==> (exists j₂₅: int ::
                      0 <= j₂₅
                      && (forall j₂₄: int ::
                            (  0 <= j₂₄
                              && j₂₄ < j₂₅
                               ==> j₂₄ < n))
                      && !(j₂₅ < n
                      )
                      && i₂₇ < n)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₂₄: int ::
              (  old(j) <= j₂₄
                && j₂₄ < j
                 ==> j₂₄ < n));
    {
      assert min <= A[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

