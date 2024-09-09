data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, i₂₈: int, found₁₀: int, i₁₂: int ::
      (  0 <= i₂₅
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₅
                 ==> (exists __VERIFIER_nondet_int₂₆: int ::
                        i₇ < 100000
                        && vectorx₂₄[i₇] == __VERIFIER_nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₅
                || vectorx₂₄[i₇] == vectorx[i₇])
        && 0 <= i₂₈
        && (forall found₉₂: int, i₉₃: int ::
              (  0 <= i₉₃
                && i₉₃ < i₂₈
                 ==> vectorx₂₄[i₉₃] == __VERIFIER_nondet_int₁
                    && i₉₃ < 100000
                    && found₉₂ == 0
                  ||   (vectorx₂₄[i₉₃] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₉₃ < 100000
                    && found₉₂ == 0))
        && i₂₈ < 100000
        && found₂₆ == 0
        && vectorx₂₄[i₂₈] == __VERIFIER_nondet_int₁
        && 0 <= i₁₂
        && i₁₂ < i₂₈ + 1
         ==> i₂₅ < 100000
          ||   vectorx₂₄[i₁₂] == __VERIFIER_nondet_int₁
            && i₁₂ < 100000
            && found₁₀ == 0
          ||   (vectorx₂₄[i₁₂] == __VERIFIER_nondet_int₁
               ==> false)
            && i₁₂ < 100000
            && found₁₀ == 0));

goal {:named "invariant forward"} (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, i₂₈: int, found₁₀: int, i₁₂: int ::
      (  0 <= i₂₅
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₅
                 ==> (exists __VERIFIER_nondet_int₂₆: int ::
                        i₇ < 100000
                        && vectorx₂₄[i₇] == __VERIFIER_nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₅
                || vectorx₂₄[i₇] == vectorx[i₇])
        && 0 <= i₂₈
        && (forall found₁₀₈: int, i₁₀₉: int ::
              (  0 <= i₁₀₉
                && i₁₀₉ < i₂₈
                 ==> vectorx₂₄[i₁₀₉] == __VERIFIER_nondet_int₁
                    && i₁₀₉ < 100000
                    && found₁₀₈ == 0
                  ||   (vectorx₂₄[i₁₀₉] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₁₀₉ < 100000
                    && found₁₀₈ == 0))
        && i₂₈ < 100000
        && found₂₆ == 0
        && 0 <= i₁₂
        && i₁₂ < i₂₈ + 1
         ==> vectorx₂₄[i₂₈] == __VERIFIER_nondet_int₁
          || i₂₅ < 100000
          ||   vectorx₂₄[i₁₂] == __VERIFIER_nondet_int₁
            && i₁₂ < 100000
            && found₁₀ == 0
          ||   (vectorx₂₄[i₁₂] == __VERIFIER_nondet_int₁
               ==> false)
            && i₁₂ < 100000
            && found₁₀ == 0));

goal {:named "assert"} (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, pos₂₇: int, i₂₈: int, vectorx₂₉: [int]int, i₃₀: int, x₃₁: int ::
      (  0 <= i₂₅
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₅
                 ==> (exists __VERIFIER_nondet_int₂₆: int ::
                        i₇ < 100000
                        && vectorx₂₄[i₇] == __VERIFIER_nondet_int₂₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₅
                || vectorx₂₄[i₇] == vectorx[i₇])
        && 0 <= i₂₈
        && (forall found₁₀: int, i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₂₈
                 ==> vectorx₂₄[i₁₂] == __VERIFIER_nondet_int₁
                    && i₁₂ < 100000
                    && found₁₀ == 0
                  ||   (vectorx₂₄[i₁₂] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₁₂ < 100000
                    && found₁₀ == 0))
        && pos₂₇ <= i₃₀
        && (forall i₁₆: int ::
              (  pos₂₇ <= i₁₆
                && i₁₆ < i₃₀
                 ==> i₁₆ < -1 + 100000
                  && vectorx₂₉[i₁₆] == vectorx₂₄[1 + i₁₆]))
        && (forall i₁₆: int ::
                  pos₂₇ <= i₁₆
                  && i₁₆ < i₃₀
                || vectorx₂₉[i₁₆] == vectorx₂₄[i₁₆])
        && 0 <= x₃₁
        && (forall x₂₁: int ::
              (  0 <= x₂₁
                && x₂₁ < x₃₁
                 ==> x₂₁ < pos₂₇))
        && x₃₁ < pos₂₇
        && vectorx₂₉[x₃₁] == __VERIFIER_nondet_int₁
         ==> found₂₆ == 0
          || i₃₀ < 100000 - 1
          || found₂₆ == 0
          || found₂₆ == 0
          || i₂₅ < 100000));

