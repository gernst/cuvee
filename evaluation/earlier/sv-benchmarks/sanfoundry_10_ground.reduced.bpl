data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₆: [int]int, i₂₇: int, found₂₈: int, i₃₀: int, found₁₁: int, i₁₃: int ::
      (  0 <= i₂₇
        && i₂₇ <= 100000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                        i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇
                        && vectorx₂₆[x₈] == __VERIFIER_nondet_int₂₆)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇)
                || vectorx₂₆[x₈] == vectorx[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> i₇ < 100000))
        && 0 <= i₃₀
        && i₃₀ <= 100000
        && (forall found₁₁₇: int, i₁₁₆: int ::
              (  i₁₁₆ <= i₁₁₆
                && 0 <= i₁₁₆
                && i₁₁₆ < i₃₀
                 ==> i₁₁₆ < 100000
                  && found₁₁₇ == 0))
        && i₃₀ < 100000
        && found₂₈ == 0
        && vectorx₂₆[i₃₀] == __VERIFIER_nondet_int₁
        && i₁₃ <= i₁₃
        && 0 <= i₁₃
        && i₁₃ < i₃₀ + 1
         ==> i₂₇ < 100000
          || found₁₁ == 0));

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₆: [int]int, i₂₇: int, found₂₈: int, i₃₀: int, found₁₁: int, i₁₃: int ::
      (  0 <= i₂₇
        && i₂₇ <= 100000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                        i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇
                        && vectorx₂₆[x₈] == __VERIFIER_nondet_int₂₆)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇)
                || vectorx₂₆[x₈] == vectorx[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> i₇ < 100000))
        && 0 <= i₃₀
        && i₃₀ <= 100000
        && (forall found₁₄₆: int, i₁₄₅: int ::
              (  i₁₄₅ <= i₁₄₅
                && 0 <= i₁₄₅
                && i₁₄₅ < i₃₀
                 ==> i₁₄₅ < 100000
                  && found₁₄₆ == 0))
        && i₃₀ < 100000
        && found₂₈ == 0
        && i₁₃ <= i₁₃
        && 0 <= i₁₃
        && i₁₃ < i₃₀ + 1
         ==> vectorx₂₆[i₃₀] == __VERIFIER_nondet_int₁
          || i₂₇ < 100000
          || found₁₁ == 0));

goal (forall vectorx: [int]int, vectorx₂₆: [int]int, i₂₇: int, found₂₈: int, pos₂₉: int, i₃₀: int ::
      (  0 <= i₂₇
        && i₂₇ <= 100000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                        i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇
                        && vectorx₂₆[x₈] == __VERIFIER_nondet_int₂₆)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇)
                || vectorx₂₆[x₈] == vectorx[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> i₇ < 100000))
        && 0 <= i₃₀
        && i₃₀ <= 100000
        && (forall found₁₁: int, i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₃₀
                 ==> i₁₃ < 100000
                  && found₁₁ == 0))
         ==> found₂₈ == 0
          || found₂₈ == 0
          || i₂₇ < 100000
          || pos₂₉ <= -1 + 100000));

goal (forall vectorx: [int]int, vectorx₂₆: [int]int, i₂₇: int, found₂₈: int, pos₂₉: int, i₃₀: int, vectorx₃₁: [int]int, i₃₂: int ::
      (  0 <= i₂₇
        && i₂₇ <= 100000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                        i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇
                        && vectorx₂₆[x₈] == __VERIFIER_nondet_int₂₆)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇)
                || vectorx₂₆[x₈] == vectorx[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> i₇ < 100000))
        && 0 <= i₃₀
        && i₃₀ <= 100000
        && (forall found₁₁: int, i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₃₀
                 ==> i₁₃ < 100000
                  && found₁₁ == 0))
        && pos₂₉ <= i₃₂
        && i₃₂ <= -1 + 100000
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && pos₂₉ <= i₁₇
                && i₁₇ < i₃₂
                 ==> (exists i₁₇: int ::
                        i₁₇ < -1 + 100000
                        && x₁₈ == i₁₇
                        && pos₂₉ <= i₁₇
                        && i₁₇ < i₃₂
                        && vectorx₃₁[x₁₈] == vectorx₂₆[1 + i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && pos₂₉ <= i₁₇
                        && i₁₇ < i₃₂)
                || vectorx₃₁[x₁₈] == vectorx₂₆[x₁₈])
        && (forall i₁₇: int ::
              (  i₁₇ <= i₁₇
                && pos₂₉ <= i₁₇
                && i₁₇ < i₃₂
                 ==> i₁₇ < -1 + 100000))
         ==> found₂₈ == 0
          || i₃₂ < 100000 - 1
          || found₂₈ == 0
          || found₂₈ == 0
          || i₂₇ < 100000
          || 0 <= pos₂₉));

goal (forall __VERIFIER_nondet_int₁: int, vectorx: [int]int, vectorx₂₆: [int]int, i₂₇: int, found₂₈: int, pos₂₉: int, i₃₀: int, vectorx₃₁: [int]int, i₃₂: int, x₃₃: int ::
      (  0 <= i₂₇
        && i₂₇ <= 100000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                        i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇
                        && vectorx₂₆[x₈] == __VERIFIER_nondet_int₂₆)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₇)
                || vectorx₂₆[x₈] == vectorx[x₈])
        && (forall i₇: int ::
              (  i₇ <= i₇
                && 0 <= i₇
                && i₇ < i₂₇
                 ==> i₇ < 100000))
        && 0 <= i₃₀
        && i₃₀ <= 100000
        && (forall found₁₁: int, i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₃₀
                 ==> i₁₃ < 100000
                  && found₁₁ == 0))
        && pos₂₉ <= i₃₂
        && i₃₂ <= -1 + 100000
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && pos₂₉ <= i₁₇
                && i₁₇ < i₃₂
                 ==> (exists i₁₇: int ::
                        i₁₇ < -1 + 100000
                        && x₁₈ == i₁₇
                        && pos₂₉ <= i₁₇
                        && i₁₇ < i₃₂
                        && vectorx₃₁[x₁₈] == vectorx₂₆[1 + i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && pos₂₉ <= i₁₇
                        && i₁₇ < i₃₂)
                || vectorx₃₁[x₁₈] == vectorx₂₆[x₁₈])
        && (forall i₁₇: int ::
              (  i₁₇ <= i₁₇
                && pos₂₉ <= i₁₇
                && i₁₇ < i₃₂
                 ==> i₁₇ < -1 + 100000))
        && 0 <= x₃₃
        && x₃₃ <= pos₂₉
        && (forall x₂₃: int ::
              (  x₂₃ <= x₂₃
                && 0 <= x₂₃
                && x₂₃ < x₃₃
                 ==> x₂₃ < pos₂₉))
        && x₃₃ < pos₂₉
        && vectorx₃₁[x₃₃] == __VERIFIER_nondet_int₁
         ==> found₂₈ == 0
          || i₃₂ < 100000 - 1
          || found₂₈ == 0
          || found₂₈ == 0
          || i₂₇ < 100000));

