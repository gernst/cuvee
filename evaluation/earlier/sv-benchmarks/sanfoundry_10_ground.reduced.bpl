data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, i₂₈: int, found₁₀: int, i₁₂: int ::
      (  0 <= i₂₅
        && i₂₅ <= 100000
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
        && i₂₈ <= 100000
        && (forall found₁₈₈: int, i₁₈₉: int ::
              (  0 <= i₁₈₉
                && i₁₈₉ < i₂₈
                 ==> vectorx₂₄[i₁₈₉] == __VERIFIER_nondet_int₁
                    && i₁₈₉ < 100000
                    && found₁₈₈ == 0
                  ||   (vectorx₂₄[i₁₈₉] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₁₈₉ < 100000
                    && found₁₈₈ == 0))
        && i₂₈ < 100000
        && found₂₆ == 0
        && vectorx₂₄[i₂₈] == __VERIFIER_nondet_int₁
        && 0 <= i₁₂
        && i₁₂ < i₂₈ + 1
        && vectorx₂₄[i₁₂] == __VERIFIER_nondet_int₁
         ==> i₂₅ < 100000
          || found₁₀ == 0));

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, i₂₈: int, found₁₀: int, i₁₂: int ::
      (  0 <= i₂₅
        && i₂₅ <= 100000
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
        && i₂₈ <= 100000
        && (forall found₂₀₆: int, i₂₀₇: int ::
              (  0 <= i₂₀₇
                && i₂₀₇ < i₂₈
                 ==> vectorx₂₄[i₂₀₇] == __VERIFIER_nondet_int₁
                    && i₂₀₇ < 100000
                    && found₂₀₆ == 0
                  ||   (vectorx₂₄[i₂₀₇] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₂₀₇ < 100000
                    && found₂₀₆ == 0))
        && i₂₈ < 100000
        && found₂₆ == 0
        && vectorx₂₄[i₂₈] == __VERIFIER_nondet_int₁
        && 0 <= i₁₂
        && i₁₂ < i₂₈ + 1
         ==> i₂₅ < 100000
          || found₁₀ == 0
          || found₁₀ == 0));

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, i₂₈: int, found₁₀: int, i₁₂: int ::
      (  0 <= i₂₅
        && i₂₅ <= 100000
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
        && i₂₈ <= 100000
        && (forall found₂₄₂: int, i₂₄₃: int ::
              (  0 <= i₂₄₃
                && i₂₄₃ < i₂₈
                 ==> vectorx₂₄[i₂₄₃] == __VERIFIER_nondet_int₁
                    && i₂₄₃ < 100000
                    && found₂₄₂ == 0
                  ||   (vectorx₂₄[i₂₄₃] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₂₄₃ < 100000
                    && found₂₄₂ == 0))
        && i₂₈ < 100000
        && found₂₆ == 0
        && 0 <= i₁₂
        && i₁₂ < i₂₈ + 1
         ==> vectorx₂₄[i₂₈] == __VERIFIER_nondet_int₁
          || i₂₅ < 100000
          || vectorx₂₄[i₁₂] == __VERIFIER_nondet_int₁
          || found₁₀ == 0));

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, i₂₈: int, found₁₀: int, i₁₂: int ::
      (  0 <= i₂₅
        && i₂₅ <= 100000
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
        && i₂₈ <= 100000
        && (forall found₂₉₀: int, i₂₉₁: int ::
              (  0 <= i₂₉₁
                && i₂₉₁ < i₂₈
                 ==> vectorx₂₄[i₂₉₁] == __VERIFIER_nondet_int₁
                    && i₂₉₁ < 100000
                    && found₂₉₀ == 0
                  ||   (vectorx₂₄[i₂₉₁] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₂₉₁ < 100000
                    && found₂₉₀ == 0))
        && i₂₈ < 100000
        && found₂₆ == 0
        && 0 <= i₁₂
        && i₁₂ < i₂₈ + 1
         ==> vectorx₂₄[i₂₈] == __VERIFIER_nondet_int₁
          || i₂₅ < 100000
          || found₁₀ == 0
          || found₁₀ == 0));

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, pos₂₇: int, i₂₈: int ::
      (  0 <= i₂₅
        && i₂₅ <= 100000
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
        && i₂₈ <= 100000
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
         ==> found₂₆ == 0
          || found₂₆ == 0
          || i₂₅ < 100000
          || pos₂₇ <= -1 + 100000));

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, pos₂₇: int, i₂₈: int, vectorx₂₉: [int]int, i₃₀: int ::
      (  0 <= i₂₅
        && i₂₅ <= 100000
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
        && i₂₈ <= 100000
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
        && i₃₀ <= -1 + 100000
        && (forall i₁₆: int ::
              (  pos₂₇ <= i₁₆
                && i₁₆ < i₃₀
                 ==> i₁₆ < -1 + 100000
                  && vectorx₂₉[i₁₆] == vectorx₂₄[1 + i₁₆]))
        && (forall i₁₆: int ::
                  pos₂₇ <= i₁₆
                  && i₁₆ < i₃₀
                || vectorx₂₉[i₁₆] == vectorx₂₄[i₁₆])
         ==> found₂₆ == 0
          || i₃₀ < 100000 - 1
          || found₂₆ == 0
          || found₂₆ == 0
          || i₂₅ < 100000
          || 0 <= pos₂₇));

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, pos₂₇: int, i₂₈: int, vectorx₂₉: [int]int, i₃₀: int, x₃₁: int ::
      (  0 <= i₂₅
        && i₂₅ <= 100000
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
        && i₂₈ <= 100000
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
        && i₃₀ <= -1 + 100000
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
        && x₃₁ <= pos₂₇
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

