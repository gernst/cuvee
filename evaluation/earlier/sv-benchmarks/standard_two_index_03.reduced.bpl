data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int ::
      (  0 <= i₁₇
        && i₁₇ <= 10000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 10000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 0 <= j₂₀
        && i₁₉ <= 10000
        && (forall i₇: int, j₈: int ::
              (  0 <= j₈
                && j₈ < j₂₀
                 ==> i₇ < 10000
                  && a₁₈[j₈] == b₁₆[i₇]))
        && (forall j₈: int ::
                  0 <= j₈
                  && j₈ < j₂₀
                || a₁₈[j₈] == a[j₈])
        && i₁₉ < 10000
         ==> i₁₇ < 10000
          || i₁₉ + 3 <= 10000));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₇: int, j₈: int ::
      (  0 <= i₁₇
        && i₁₇ <= 10000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 10000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 0 <= j₂₀
        && i₁₉ <= 10000
        && (forall i₁₀₇: int, j₁₀₈: int ::
              (  0 <= j₁₀₈
                && j₁₀₈ < j₂₀
                 ==> i₁₀₇ < 10000
                  && a₁₈[j₁₀₈] == b₁₆[i₁₀₇]))
        && (forall j₁₀₉: int ::
                  0 <= j₁₀₉
                  && j₁₀₉ < j₂₀
                || a₁₈[j₁₀₉] == a[j₁₀₉])
        && i₁₉ < 10000
        && 0 <= j₈
        && j₈ < j₂₀ + 1
         ==> i₁₇ < 10000
          || i₇ < 10000));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₇: int, j₈: int ::
      (  0 <= i₁₇
        && i₁₇ <= 10000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 10000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 0 <= j₂₀
        && i₁₉ <= 10000
        && (forall i₁₁₉: int, j₁₂₀: int ::
              (  0 <= j₁₂₀
                && j₁₂₀ < j₂₀
                 ==> i₁₁₉ < 10000
                  && a₁₈[j₁₂₀] == b₁₆[i₁₁₉]))
        && (forall j₁₂₁: int ::
                  0 <= j₁₂₁
                  && j₁₂₁ < j₂₀
                || a₁₈[j₁₂₁] == a[j₁₂₁])
        && i₁₉ < 10000
        && 0 <= j₈
        && j₈ < j₂₀ + 1
         ==> i₁₇ < 10000
          || a₁₈[j₂₀ := b₁₆[i₁₉]][j₈] == b₁₆[i₇]));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₂₁: int, j₂₂: int ::
      (  0 <= i₁₇
        && i₁₇ <= 10000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 10000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 0 <= j₂₀
        && i₁₉ <= 10000
        && (forall i₇: int, j₈: int ::
              (  0 <= j₈
                && j₈ < j₂₀
                 ==> i₇ < 10000
                  && a₁₈[j₈] == b₁₆[i₇]))
        && (forall j₈: int ::
                  0 <= j₈
                  && j₈ < j₂₀
                || a₁₈[j₈] == a[j₈])
        && 0 <= j₂₂
        && i₂₁ <= 10000
        && (forall i₁₂: int, j₁₃: int ::
              (  0 <= j₁₃
                && j₁₃ < j₂₂
                 ==> i₁₂ < 10000))
        && i₂₁ < 10000
         ==> i₁₉ < 10000
          || i₁₇ < 10000
          || a₁₈[j₂₂] == b₁₆[3 * j₂₂ + 1]));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₂₁: int, j₂₂: int ::
      (  0 <= i₁₇
        && i₁₇ <= 10000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 10000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 0 <= j₂₀
        && i₁₉ <= 10000
        && (forall i₇: int, j₈: int ::
              (  0 <= j₈
                && j₈ < j₂₀
                 ==> i₇ < 10000
                  && a₁₈[j₈] == b₁₆[i₇]))
        && (forall j₈: int ::
                  0 <= j₈
                  && j₈ < j₂₀
                || a₁₈[j₈] == a[j₈])
        && 0 <= j₂₂
        && i₂₁ <= 10000
        && (forall i₁₂: int, j₁₃: int ::
              (  0 <= j₁₃
                && j₁₃ < j₂₂
                 ==> i₁₂ < 10000))
        && i₂₁ < 10000
         ==> i₁₉ < 10000
          || i₁₇ < 10000
          || i₂₁ + 3 <= 10000));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₂₁: int, j₂₂: int, i₁₂: int, j₁₃: int ::
      (  0 <= i₁₇
        && i₁₇ <= 10000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 10000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 0 <= j₂₀
        && i₁₉ <= 10000
        && (forall i₇: int, j₈: int ::
              (  0 <= j₈
                && j₈ < j₂₀
                 ==> i₇ < 10000
                  && a₁₈[j₈] == b₁₆[i₇]))
        && (forall j₈: int ::
                  0 <= j₈
                  && j₈ < j₂₀
                || a₁₈[j₈] == a[j₈])
        && 0 <= j₂₂
        && i₂₁ <= 10000
        && (forall i₁₉₉: int, j₂₀₀: int ::
              (  0 <= j₂₀₀
                && j₂₀₀ < j₂₂
                 ==> i₁₉₉ < 10000))
        && i₂₁ < 10000
        && 0 <= j₁₃
        && j₁₃ < j₂₂ + 1
         ==> i₁₉ < 10000
          || i₁₇ < 10000
          || i₁₂ < 10000));

