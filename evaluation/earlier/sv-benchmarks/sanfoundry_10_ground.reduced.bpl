data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, i₂₈: int, found₁₀: int, i₁₂: int ::
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
        && (forall found₁₇₆: int, i₁₇₇: int ::
              (  0 <= i₁₇₇
                && i₁₇₇ < i₂₈
                 ==> vectorx₂₄[i₁₇₇] == __VERIFIER_nondet_int₁
                    && i₁₇₇ < 100000
                    && found₁₇₆ == 0
                  ||   (vectorx₂₄[i₁₇₇] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₁₇₇ < 100000
                    && found₁₇₆ == 0))
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
        && (forall found₁₉₄: int, i₁₉₅: int ::
              (  0 <= i₁₉₅
                && i₁₉₅ < i₂₈
                 ==> vectorx₂₄[i₁₉₅] == __VERIFIER_nondet_int₁
                    && i₁₉₅ < 100000
                    && found₁₉₄ == 0
                  ||   (vectorx₂₄[i₁₉₅] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₁₉₅ < 100000
                    && found₁₉₄ == 0))
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
        && (forall found₂₂₄: int, i₂₂₅: int ::
              (  0 <= i₂₂₅
                && i₂₂₅ < i₂₈
                 ==> vectorx₂₄[i₂₂₅] == __VERIFIER_nondet_int₁
                    && i₂₂₅ < 100000
                    && found₂₂₄ == 0
                  ||   (vectorx₂₄[i₂₂₅] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₂₂₅ < 100000
                    && found₂₂₄ == 0))
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
        && (forall found₂₇₂: int, i₂₇₃: int ::
              (  0 <= i₂₇₃
                && i₂₇₃ < i₂₈
                 ==> vectorx₂₄[i₂₇₃] == __VERIFIER_nondet_int₁
                    && i₂₇₃ < 100000
                    && found₂₇₂ == 0
                  ||   (vectorx₂₄[i₂₇₃] == __VERIFIER_nondet_int₁
                       ==> false)
                    && i₂₇₃ < 100000
                    && found₂₇₂ == 0))
        && i₂₈ < 100000
        && found₂₆ == 0
        && 0 <= i₁₂
        && i₁₂ < i₂₈ + 1
         ==> vectorx₂₄[i₂₈] == __VERIFIER_nondet_int₁
          || i₂₅ < 100000
          || found₁₀ == 0
          || found₁₀ == 0));

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₄: [int]int, i₂₅: int, found₂₆: int, pos₂₇: int, i₂₈: int, vectorx₂₉: [int]int, i₃₀: int, x₃₁: int ::
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

