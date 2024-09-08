data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int, aa₁₁: [int]int, i₁₂: int ::
      (  0 <= i₁₂
        && i₁₂ <= 100000
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₂
                 ==> (exists __VERIFIER_nondet_int₁₂: int ::
                        i₃ < 100000
                        && aa₁₁[i₃] == __VERIFIER_nondet_int₁₂)))
        && (forall i₃: int ::
                  0 <= i₃
                  && i₃ < i₁₂
                || aa₁₁[i₃] == aa[i₃])
         ==> i₁₂ < 100000
          || 0 <= 1 + aa₁₁[0]));

goal (forall aa: [int]int, aa₁₁: [int]int, i₁₂: int, a₁₃: int ::
      (  0 <= i₁₂
        && i₁₂ <= 100000
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₂
                 ==> (exists __VERIFIER_nondet_int₁₂: int ::
                        i₃ < 100000
                        && aa₁₁[i₃] == __VERIFIER_nondet_int₁₂)))
        && (forall i₃: int ::
                  0 <= i₃
                  && i₃ < i₁₂
                || aa₁₁[i₃] == aa[i₃])
        && 0 <= a₁₃
        && 0 <= 1 + aa₁₁[a₁₃]
        && (forall a₆: int ::
              (  0 <= a₆
                && a₆ < a₁₃
                 ==> 0 <= aa₁₁[a₆]))
        && 0 <= aa₁₁[a₁₃]
         ==> i₁₂ < 100000
          || 0 <= 1 + aa₁₁[a₁₃ + 1]));

