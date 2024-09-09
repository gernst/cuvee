data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, j₁₁: int, i₁₂: int ::
      (  0 <= i₂₃
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
        && (forall j₂₄₄: int, i₂₄₅: int ::
              (  0 <= j₂₄₄
                && j₂₄₄ < j₂₅
                && 0 <= i₂₄₅
                && i₂₄₅ < i₂₆
                 ==> A₂₁[i₂₄₅] == B₂₂[i₂₄₅]
                    && i₂₄₅ < 100000
                    && C₂₄[j₂₄₄] == i₂₄₅
                  ||   (A₂₁[i₂₄₅] == B₂₂[i₂₄₅]
                       ==> false)
                    && i₂₄₅ < 100000))
        && (forall j₂₄₆: int, i₂₄₇: int ::
                  0 <= j₂₄₆
                  && j₂₄₆ < j₂₅
                  && 0 <= i₂₄₇
                  && i₂₄₇ < i₂₆
                || C₂₄[j₂₄₆] == C[j₂₄₆])
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
        && (forall j₂₉₀: int, i₂₉₁: int ::
              (  0 <= j₂₉₀
                && j₂₉₀ < j₂₅
                && 0 <= i₂₉₁
                && i₂₉₁ < i₂₆
                 ==> A₂₁[i₂₉₁] == B₂₂[i₂₉₁]
                    && i₂₉₁ < 100000
                    && C₂₄[j₂₉₀] == i₂₉₁
                  ||   (A₂₁[i₂₉₁] == B₂₂[i₂₉₁]
                       ==> false)
                    && i₂₉₁ < 100000))
        && (forall j₂₉₂: int, i₂₉₃: int ::
                  0 <= j₂₉₂
                  && j₂₉₂ < j₂₅
                  && 0 <= i₂₉₃
                  && i₂₉₃ < i₂₆
                || C₂₄[j₂₉₂] == C[j₂₉₂])
        && i₂₆ < 100000
        && A₂₁[i₂₆] == B₂₂[i₂₆]
         ==> 0 <= i₁₂
          || i₂₃ < 100000
          || C₂₄[j₂₅ := i₂₆][j₁₁] == C[j₁₁]));

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, j₁₁: int, i₁₂: int ::
      (  0 <= i₂₃
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
        && (forall j₃₀₅: int, i₃₀₆: int ::
              (  0 <= j₃₀₅
                && j₃₀₅ < j₂₅
                && 0 <= i₃₀₆
                && i₃₀₆ < i₂₆
                 ==> A₂₁[i₃₀₆] == B₂₂[i₃₀₆]
                    && i₃₀₆ < 100000
                    && C₂₄[j₃₀₅] == i₃₀₆
                  ||   (A₂₁[i₃₀₆] == B₂₂[i₃₀₆]
                       ==> false)
                    && i₃₀₆ < 100000))
        && (forall j₃₀₇: int, i₃₀₈: int ::
                  0 <= j₃₀₇
                  && j₃₀₇ < j₂₅
                  && 0 <= i₃₀₈
                  && i₃₀₈ < i₂₆
                || C₂₄[j₃₀₇] == C[j₃₀₇])
        && i₂₆ < 100000
        && A₂₁[i₂₆] == B₂₂[i₂₆]
         ==> i₁₂ < i₂₆ + 1
          || i₂₃ < 100000
          || C₂₄[j₂₅ := i₂₆][j₁₁] == C[j₁₁]));

goal (forall A: [int]int, B: [int]int, C: [int]int, A₂₁: [int]int, B₂₂: [int]int, i₂₃: int, C₂₄: [int]int, j₂₅: int, i₂₆: int, x₂₇: int ::
      (  0 <= i₂₃
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

