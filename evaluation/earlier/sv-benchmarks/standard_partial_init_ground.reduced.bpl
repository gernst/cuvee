data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, j₁₁: int, i₁₂: int ::
      (  0 <= i₂₃
        && i₂₃ <= 100000
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₃
                 ==> (exists __VERIFIER_nondet_int₁₅: int, __VERIFIER_nondet_int₂₆: int ::
                        i₇ < 100000
                        && A₂₁[i₇] == __VERIFIER_nondet_int₁₅
                        && B₂₂[i₇] == __VERIFIER_nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₃
                ||   A₂₁[i₇] == A[i₇]
                  && B₂₂[i₇] == B[i₇])
        && 0 <= j₂₅
        && 0 <= i₂₆
        && i₂₆ <= 100000
        && (forall j₂₆₃: int, i₂₆₄: int ::
              (  0 <= j₂₆₃
                && j₂₆₃ < j₂₅
                && 0 <= i₂₆₄
                && i₂₆₄ < i₂₆
                 ==> A₂₁[i₂₆₄] == B₂₂[i₂₆₄]
                    && i₂₆₄ < 100000
                    && C₂₄[j₂₆₃] == i₂₆₄
                  ||   (A₂₁[i₂₆₄] == B₂₂[i₂₆₄]
                       ==> false)
                    && i₂₆₄ < 100000))
        && (forall j₂₆₅: int, i₂₆₆: int ::
                  0 <= j₂₆₅
                  && j₂₆₅ < j₂₅
                  && 0 <= i₂₆₆
                  && i₂₆₆ < i₂₆
                || C₂₄[j₂₆₅] == C[j₂₆₅])
        && i₂₆ < 100000
        && A₂₁[i₂₆] == B₂₂[i₂₆]
        && 0 <= j₁₁
        && j₁₁ < j₂₅ + 1
        && 0 <= i₁₂
        && i₁₂ < i₂₆ + 1
        && A₂₁[i₁₂] == B₂₂[i₁₂]
         ==> i₂₃ < 100000
          || C₂₄[j₂₅ := i₂₆][j₁₁] == i₁₂));

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, j₁₁: int, i₁₂: int ::
      (  0 <= i₂₃
        && i₂₃ <= 100000
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₃
                 ==> (exists __VERIFIER_nondet_int₁₅: int, __VERIFIER_nondet_int₂₆: int ::
                        i₇ < 100000
                        && A₂₁[i₇] == __VERIFIER_nondet_int₁₅
                        && B₂₂[i₇] == __VERIFIER_nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₃
                ||   A₂₁[i₇] == A[i₇]
                  && B₂₂[i₇] == B[i₇])
        && 0 <= j₂₅
        && 0 <= i₂₆
        && i₂₆ <= 100000
        && (forall j₃₀₉: int, i₃₁₀: int ::
              (  0 <= j₃₀₉
                && j₃₀₉ < j₂₅
                && 0 <= i₃₁₀
                && i₃₁₀ < i₂₆
                 ==> A₂₁[i₃₁₀] == B₂₂[i₃₁₀]
                    && i₃₁₀ < 100000
                    && C₂₄[j₃₀₉] == i₃₁₀
                  ||   (A₂₁[i₃₁₀] == B₂₂[i₃₁₀]
                       ==> false)
                    && i₃₁₀ < 100000))
        && (forall j₃₁₁: int, i₃₁₂: int ::
                  0 <= j₃₁₁
                  && j₃₁₁ < j₂₅
                  && 0 <= i₃₁₂
                  && i₃₁₂ < i₂₆
                || C₂₄[j₃₁₁] == C[j₃₁₁])
        && i₂₆ < 100000
        && A₂₁[i₂₆] == B₂₂[i₂₆]
         ==> 0 <= i₁₂
          || i₂₃ < 100000
          || C₂₄[j₂₅ := i₂₆][j₁₁] == C[j₁₁]));

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, j₁₁: int, i₁₂: int ::
      (  0 <= i₂₃
        && i₂₃ <= 100000
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₃
                 ==> (exists __VERIFIER_nondet_int₁₅: int, __VERIFIER_nondet_int₂₆: int ::
                        i₇ < 100000
                        && A₂₁[i₇] == __VERIFIER_nondet_int₁₅
                        && B₂₂[i₇] == __VERIFIER_nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₃
                ||   A₂₁[i₇] == A[i₇]
                  && B₂₂[i₇] == B[i₇])
        && 0 <= j₂₅
        && 0 <= i₂₆
        && i₂₆ <= 100000
        && (forall j₃₂₄: int, i₃₂₅: int ::
              (  0 <= j₃₂₄
                && j₃₂₄ < j₂₅
                && 0 <= i₃₂₅
                && i₃₂₅ < i₂₆
                 ==> A₂₁[i₃₂₅] == B₂₂[i₃₂₅]
                    && i₃₂₅ < 100000
                    && C₂₄[j₃₂₄] == i₃₂₅
                  ||   (A₂₁[i₃₂₅] == B₂₂[i₃₂₅]
                       ==> false)
                    && i₃₂₅ < 100000))
        && (forall j₃₂₆: int, i₃₂₇: int ::
                  0 <= j₃₂₆
                  && j₃₂₆ < j₂₅
                  && 0 <= i₃₂₇
                  && i₃₂₇ < i₂₆
                || C₂₄[j₃₂₆] == C[j₃₂₆])
        && i₂₆ < 100000
        && A₂₁[i₂₆] == B₂₂[i₂₆]
         ==> i₁₂ < i₂₆ + 1
          || i₂₃ < 100000
          || C₂₄[j₂₅ := i₂₆][j₁₁] == C[j₁₁]));

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, x₂₇: int ::
      (  0 <= i₂₃
        && i₂₃ <= 100000
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₃
                 ==> (exists __VERIFIER_nondet_int₁₅: int, __VERIFIER_nondet_int₂₆: int ::
                        i₇ < 100000
                        && A₂₁[i₇] == __VERIFIER_nondet_int₁₅
                        && B₂₂[i₇] == __VERIFIER_nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₃
                ||   A₂₁[i₇] == A[i₇]
                  && B₂₂[i₇] == B[i₇])
        && 0 <= j₂₅
        && 0 <= i₂₆
        && i₂₆ <= 100000
        && (forall j₁₁: int, i₁₂: int ::
              (  0 <= j₁₁
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
                  0 <= j₁₁
                  && j₁₁ < j₂₅
                  && 0 <= i₁₂
                  && i₁₂ < i₂₆
                || C₂₄[j₁₁] == C[j₁₁])
        && 0 <= x₂₇
        && x₂₇ <= j₂₅
        && (forall x₁₇: int ::
              (  0 <= x₁₇
                && x₁₇ < x₂₇
                 ==> x₁₇ < j₂₅))
        && x₂₇ < j₂₅
         ==> i₂₆ < 100000
          || i₂₃ < 100000
          || C₂₄[x₂₇] <= x₂₇ + i₂₆ - j₂₅));

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, x₂₇: int, x₂₈: int ::
      (  0 <= i₂₃
        && i₂₃ <= 100000
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₃
                 ==> (exists __VERIFIER_nondet_int₁₅: int, __VERIFIER_nondet_int₂₆: int ::
                        i₇ < 100000
                        && A₂₁[i₇] == __VERIFIER_nondet_int₁₅
                        && B₂₂[i₇] == __VERIFIER_nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₃
                ||   A₂₁[i₇] == A[i₇]
                  && B₂₂[i₇] == B[i₇])
        && 0 <= j₂₅
        && 0 <= i₂₆
        && i₂₆ <= 100000
        && (forall j₁₁: int, i₁₂: int ::
              (  0 <= j₁₁
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
                  0 <= j₁₁
                  && j₁₁ < j₂₅
                  && 0 <= i₁₂
                  && i₁₂ < i₂₆
                || C₂₄[j₁₁] == C[j₁₁])
        && 0 <= x₂₇
        && x₂₇ <= j₂₅
        && (forall x₁₇: int ::
              (  0 <= x₁₇
                && x₁₇ < x₂₇
                 ==> x₁₇ < j₂₅))
        && 0 <= x₂₈
        && x₂₈ <= j₂₅
        && (forall x₁₉: int ::
              (  0 <= x₁₉
                && x₁₉ < x₂₈
                 ==> x₁₉ < j₂₅))
        && x₂₈ < j₂₅
         ==> x₂₇ < j₂₅
          || i₂₆ < 100000
          || i₂₃ < 100000
          || x₂₈ <= C₂₄[x₂₈]));

