data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int ::
      (  0 <= i₂₃
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₃
                 ==> (exists nondet_int₁₅: int, nondet_int₂₆: int ::
                        i₇ < 100000
                        && A₂₁[i₇] == nondet_int₁₅
                        && B₂₂[i₇] == nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₃
                ||   A₂₁[i₇] == A[i₇]
                  && B₂₂[i₇] == B[i₇])
        && j₂₅ + 0 == i₂₆ + 0
        && 0 <= j₂₅
        && 0 <= i₂₆
        && (forall j₁₁: int, i₁₂: int ::
              (  j₁₁ + j₁₁ == i₁₂ + i₁₂
                && 0 <= j₁₁
                && j₁₁ < j₂₅
                && 0 <= i₁₂
                && i₁₂ < i₂₆
                 ==> A₂₁[i₁₂] == B₂₂[i₁₂]
                    && i₁₂ < 100000
                    && C₂₄[j₁₁] == i₁₂
                  ||   (A₂₁[i₁₂] == B₂₂[i₁₂]
                       ==> false)
                    && i₁₂ < 100000))
        && (forall j₁₁: int, i₁₂: int ::
              (j₁₁ + j₁₁ == i₁₂ + i₁₂
                 ==> 0 <= j₁₁
                    && j₁₁ < j₂₅
                    && 0 <= i₁₂
                    && i₁₂ < i₂₆
                  || C₂₄[j₁₁] == C[j₁₁]))
        && i₂₆ < 100000
         ==> A₂₁[i₂₆] == B₂₂[i₂₆]
          || i₂₃ < 100000
          || j₂₅ + 0 == i₂₆ + 1 + 0));

goal {:named "assert"} (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, x₂₇: int ::
      (  0 <= i₂₃
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₃
                 ==> (exists nondet_int₁₅: int, nondet_int₂₆: int ::
                        i₇ < 100000
                        && A₂₁[i₇] == nondet_int₁₅
                        && B₂₂[i₇] == nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₃
                ||   A₂₁[i₇] == A[i₇]
                  && B₂₂[i₇] == B[i₇])
        && j₂₅ + 0 == i₂₆ + 0
        && 0 <= j₂₅
        && 0 <= i₂₆
        && (forall j₁₁: int, i₁₂: int ::
              (  j₁₁ + j₁₁ == i₁₂ + i₁₂
                && 0 <= j₁₁
                && j₁₁ < j₂₅
                && 0 <= i₁₂
                && i₁₂ < i₂₆
                 ==> A₂₁[i₁₂] == B₂₂[i₁₂]
                    && i₁₂ < 100000
                    && C₂₄[j₁₁] == i₁₂
                  ||   (A₂₁[i₁₂] == B₂₂[i₁₂]
                       ==> false)
                    && i₁₂ < 100000))
        && (forall j₁₁: int, i₁₂: int ::
              (j₁₁ + j₁₁ == i₁₂ + i₁₂
                 ==> 0 <= j₁₁
                    && j₁₁ < j₂₅
                    && 0 <= i₁₂
                    && i₁₂ < i₂₆
                  || C₂₄[j₁₁] == C[j₁₁]))
        && 0 <= x₂₇
        && (forall x₁₇: int ::
              (  0 <= x₁₇
                && x₁₇ < x₂₇
                 ==> x₁₇ < j₂₅))
        && x₂₇ < j₂₅
         ==> i₂₆ < 100000
          || i₂₃ < 100000
          || C₂₄[x₂₇] <= x₂₇ + i₂₆ - j₂₅));

goal {:named "assert"} (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, x₂₇: int, x₂₈: int ::
      (  0 <= i₂₃
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₃
                 ==> (exists nondet_int₁₅: int, nondet_int₂₆: int ::
                        i₇ < 100000
                        && A₂₁[i₇] == nondet_int₁₅
                        && B₂₂[i₇] == nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₃
                ||   A₂₁[i₇] == A[i₇]
                  && B₂₂[i₇] == B[i₇])
        && j₂₅ + 0 == i₂₆ + 0
        && 0 <= j₂₅
        && 0 <= i₂₆
        && (forall j₁₁: int, i₁₂: int ::
              (  j₁₁ + j₁₁ == i₁₂ + i₁₂
                && 0 <= j₁₁
                && j₁₁ < j₂₅
                && 0 <= i₁₂
                && i₁₂ < i₂₆
                 ==> A₂₁[i₁₂] == B₂₂[i₁₂]
                    && i₁₂ < 100000
                    && C₂₄[j₁₁] == i₁₂
                  ||   (A₂₁[i₁₂] == B₂₂[i₁₂]
                       ==> false)
                    && i₁₂ < 100000))
        && (forall j₁₁: int, i₁₂: int ::
              (j₁₁ + j₁₁ == i₁₂ + i₁₂
                 ==> 0 <= j₁₁
                    && j₁₁ < j₂₅
                    && 0 <= i₁₂
                    && i₁₂ < i₂₆
                  || C₂₄[j₁₁] == C[j₁₁]))
        && 0 <= x₂₇
        && (forall x₁₇: int ::
              (  0 <= x₁₇
                && x₁₇ < x₂₇
                 ==> x₁₇ < j₂₅))
        && 0 <= x₂₈
        && (forall x₁₉: int ::
              (  0 <= x₁₉
                && x₁₉ < x₂₈
                 ==> x₁₉ < j₂₅))
        && x₂₈ < j₂₅
         ==> x₂₇ < j₂₅
          || i₂₆ < 100000
          || i₂₃ < 100000
          || x₂₈ <= C₂₄[x₂₈]));

