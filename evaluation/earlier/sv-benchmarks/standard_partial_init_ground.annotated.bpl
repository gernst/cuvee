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
  var A: [int]int;
  var B: [int]int;
  var C: [int]int;
  var i: int;
  var j: int := 0;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> (exists nondet_int₁₅: int, nondet_int₂₆: int ::
                      -2147483648 <= nondet_int₂₆
                      && nondet_int₂₆ < 2147483648
                      && -2147483648 <= nondet_int₁₅
                      && nondet_int₁₅ < 2147483648
                      && i₇ < 100000
                      && A[i₇] == nondet_int₁₅
                      && B[i₇] == nondet_int₂₆)))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> A[i₇] == old(A)[i₇]
                && B[i₇] == old(B)[i₇]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    A[i] := nondet_int₁;
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    B[i] := nondet_int₂;
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant j + old(j) == i + old(i)
      && old(j) <= j
      && old(i) <= i
      && (forall j₁₁: int, i₁₂: int ::
            (  old(j₁₁) + j₁₁ == old(i₁₂) + i₁₂
              && old(j) <= j₁₁
              && j₁₁ < j
              && old(i) <= i₁₂
              && i₁₂ < i
               ==> A[i₁₂] == B[i₁₂]
                  && i₁₂ < 100000
                  && C[j₁₁] == i₁₂
                ||   A[i₁₂] != B[i₁₂]
                  && i₁₂ < 100000))
      && (forall j₁₁: int, i₁₂: int ::
            (  old(j₁₁) + j₁₁ == old(i₁₂) + i₁₂
              && !(  old(j) <= j₁₁
                && j₁₁ < j
                && old(i) <= i₁₂
                && i₁₂ < i
              )
               ==> C[j₁₁] == old(C)[j₁₁]));
  {
    if(A[i] == B[i]) {
      C[j] := i;
      j := j + 1;
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < j)
    decreases j - x;
    invariant old(x) <= x
      && (forall x₁₇: int ::
            (  old(x) <= x₁₇
              && x₁₇ < x
               ==> x₁₇ < j));
  {
    assert C[x] <= x + i - j;
    x := x + 1;
  }
  x := 0;
  while(x < j)
    decreases j - x;
    invariant old(x) <= x
      && (forall x₁₉: int ::
            (  old(x) <= x₁₉
              && x₁₉ < x
               ==> x₁₉ < j));
  {
    assert x <= C[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

