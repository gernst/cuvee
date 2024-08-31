data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

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
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₈: int ::
            ((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                      i₇ < 100000
                      && x₈ == i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && A[x₈] == __VERIFIER_nondet_int₁₅)))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> A[x₈] == old(A[x₈])))
      && (forall x₉: int ::
            ((exists i₇: int ::
                    x₉ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                      i₇ < 100000
                      && x₉ == i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && B[x₉] == __VERIFIER_nondet_int₂₆)))
      && (forall x₉: int ::
            (!((exists i₇: int ::
                    x₉ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> B[x₉] == old(B[x₉])))
      && (forall i₇: int ::
            (  old(i₇) <= i₇
              && old(i) <= i₇
              && i₇ < i
               ==> i₇ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    A := A[i := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    B := B[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(j) <= j
      && old(i) <= i
      && i <= 100000
      && (forall x₁₅: int ::
            ((exists j₁₃: int ::
                    x₁₅ == j₁₃
                    && old(j) <= j₁₃
                    && j₁₃ < j)
               ==> (exists j₁₃: int, i₁₄: int ::
                      A[i₁₄] == B[i₁₄]
                      && i₁₄ < 100000
                      && x₁₅ == j₁₃
                      && old(j) <= j₁₃
                      && j₁₃ < j
                      && old(i) <= i₁₄
                      && i₁₄ < i
                      && C[x₁₅] == i₁₄)))
      && (forall x₁₅: int ::
            (!((exists j₁₃: int ::
                    x₁₅ == j₁₃
                    && old(j) <= j₁₃
                    && j₁₃ < j)
            )
               ==> C[x₁₅] == old(C[x₁₅])))
      && (forall j₁₃: int, i₁₄: int ::
            (  old(j₁₃) <= j₁₃
              && old(i₁₄) <= i₁₄
              && old(j) <= j₁₃
              && j₁₃ < j
              && old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 100000));
  {
    if(A[i] == B[i]) {
      C := C[j := i];
      j := j + 1;
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < j)
    decreases j - x;
    invariant true
      && old(x) <= x
      && x <= j
      && (forall x₂₀: int ::
            (  old(x₂₀) <= x₂₀
              && old(x) <= x₂₀
              && x₂₀ < x
               ==> x₂₀ < j));
  {
    assert C[x] <= x + i - j;
    x := x + 1;
  }
  x := 0;
  while(x < j)
    decreases j - x;
    invariant true
      && old(x) <= x
      && x <= j
      && (forall x₂₂: int ::
            (  old(x₂₂) <= x₂₂
              && old(x) <= x₂₂
              && x₂₂ < x
               ==> x₂₂ < j));
  {
    assert x <= C[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

