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
  var q: int;
  var s: int;
  var A: [int][int]int;
  var C: int;
  assume 0 <= C && C < 4294967296;
  havoc q;
  assume -2147483648 <= q && q < 2147483648;
  havoc s;
  assume -2147483648 <= s && s < 2147483648;
  i := 0;
  j := 0;
  assume q < m;
  assume s < n;
  while(i < q)
    decreases q - i;
    invariant old(i) <= i
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> (exists A₁₀: [int][int]int, j₁₁: int ::
                      0 <= j₁₁
                      && (forall j₉: int ::
                            (  0 <= j₉
                              && j₉ < j₁₁
                               ==> j₉ < s
                                && A₁₀[i₁₃][j₉] == i₁₃ + j₉ + C))
                      && (forall j₉: int ::
                            (!(  0 <= j₉
                              && j₉ < j₁₁
                            )
                               ==> A₁₀[i₁₃][j₉] == A[i₁₃][j₉]))
                      && !(j₁₁ < s
                      )
                      && i₁₃ < q)));
  {
    j := 0;
    while(j < s)
      decreases s - j;
      invariant old(j) <= j
        && (forall j₉: int ::
              (  old(j) <= j₉
                && j₉ < j
                 ==> j₉ < s
                  && A[i][j₉] == j₉ + i + C))
        && (forall j₉: int ::
              (!(  old(j) <= j₉
                && j₉ < j
              )
                 ==> A[i][j₉] == old(A)[i][j₉]));
    {
      A[i][j] := i + j + C;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < q)
    decreases q - i;
    invariant old(i) <= i
      && (forall i₂₀: int ::
            (  old(i) <= i₂₀
              && i₂₀ < i
               ==> (exists j₁₈: int ::
                      0 <= j₁₈
                      && (forall j₁₇: int ::
                            (  0 <= j₁₇
                              && j₁₇ < j₁₈
                               ==> j₁₇ < s))
                      && !(j₁₈ < s
                      )
                      && i₂₀ < q)));
  {
    j := 0;
    while(j < s)
      decreases s - j;
      invariant old(j) <= j
        && (forall j₁₇: int ::
              (  old(j) <= j₁₇
                && j₁₇ < j
                 ==> j₁₇ < s));
    {
      assert A[i][j] == i + j + C;
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

