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
  var C: int;
  assume -2147483648 <= C && C < 2147483648;
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> (exists A₆: [int][int]int, j₇: int ::
                      0 <= j₇
                      && (forall j₅: int ::
                            (  0 <= j₅
                              && j₅ < j₇
                               ==> j₅ < n
                                && A₆[i₉][j₅] == C))
                      && (forall j₅: int ::
                            (!(  0 <= j₅
                              && j₅ < j₇
                            )
                               ==> A₆[i₉][j₅] == A[i₉][j₅]))
                      && !(j₇ < n
                      )
                      && i₉ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₅: int ::
              (  old(j) <= j₅
                && j₅ < j
                 ==> j₅ < n
                  && A[i][j₅] == C))
        && (forall j₅: int ::
              (!(  old(j) <= j₅
                && j₅ < j
              )
                 ==> A[i][j₅] == old(A)[i][j₅]));
    {
      A[i][j] := C;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m)
    decreases m - i;
    invariant old(i) <= i
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> (exists j₁₄: int ::
                      0 <= j₁₄
                      && (forall j₁₃: int ::
                            (  0 <= j₁₃
                              && j₁₃ < j₁₄
                               ==> j₁₃ < n))
                      && !(j₁₄ < n
                      )
                      && i₁₆ < m)));
  {
    j := 0;
    while(j < n)
      decreases n - j;
      invariant old(j) <= j
        && (forall j₁₃: int ::
              (  old(j) <= j₁₃
                && j₁₃ < j
                 ==> j₁₃ < n));
    {
      assert A[i][j] == C;
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

