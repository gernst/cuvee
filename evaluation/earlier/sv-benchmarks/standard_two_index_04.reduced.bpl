data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₇: int, j₈: int ::
      (  0 <= i₁₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 100000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 1 <= i₁₉
        && 0 <= j₂₀
        && (forall i₁₀₄: int, j₁₀₅: int ::
              (  0 <= j₁₀₅
                && j₁₀₅ < j₂₀
                 ==> i₁₀₄ < 100000
                  && a₁₈[j₁₀₅] == b₁₆[i₁₀₄]))
        && (forall j₁₀₆: int ::
                  0 <= j₁₀₆
                  && j₁₀₆ < j₂₀
                || a₁₈[j₁₀₆] == a[j₁₀₆])
        && i₁₉ < 100000
        && 0 <= j₈
        && j₈ < j₂₀ + 1
         ==> i₁₇ < 100000
          || i₇ < 100000));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₇: int, j₈: int ::
      (  0 <= i₁₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 100000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 1 <= i₁₉
        && 0 <= j₂₀
        && (forall i₁₁₆: int, j₁₁₇: int ::
              (  0 <= j₁₁₇
                && j₁₁₇ < j₂₀
                 ==> i₁₁₆ < 100000
                  && a₁₈[j₁₁₇] == b₁₆[i₁₁₆]))
        && (forall j₁₁₈: int ::
                  0 <= j₁₁₈
                  && j₁₁₈ < j₂₀
                || a₁₈[j₁₁₈] == a[j₁₁₈])
        && i₁₉ < 100000
        && 0 <= j₈
        && j₈ < j₂₀ + 1
         ==> i₁₇ < 100000
          || a₁₈[j₂₀ := b₁₆[i₁₉]][j₈] == b₁₆[i₇]));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₂₁: int, j₂₂: int ::
      (  0 <= i₁₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 100000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 1 <= i₁₉
        && 0 <= j₂₀
        && (forall i₇: int, j₈: int ::
              (  0 <= j₈
                && j₈ < j₂₀
                 ==> i₇ < 100000
                  && a₁₈[j₈] == b₁₆[i₇]))
        && (forall j₈: int ::
                  0 <= j₈
                  && j₈ < j₂₀
                || a₁₈[j₈] == a[j₈])
        && 1 <= i₂₁
        && 0 <= j₂₂
        && (forall i₁₂: int, j₁₃: int ::
              (  0 <= j₁₃
                && j₁₃ < j₂₂
                 ==> i₁₂ < 100000))
        && i₂₁ < 100000
         ==> i₁₉ < 100000
          || i₁₇ < 100000
          || a₁₈[j₂₂] == b₁₆[4 * j₂₂ + 1]));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₂₁: int, j₂₂: int, i₁₂: int, j₁₃: int ::
      (  0 <= i₁₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 100000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 1 <= i₁₉
        && 0 <= j₂₀
        && (forall i₇: int, j₈: int ::
              (  0 <= j₈
                && j₈ < j₂₀
                 ==> i₇ < 100000
                  && a₁₈[j₈] == b₁₆[i₇]))
        && (forall j₈: int ::
                  0 <= j₈
                  && j₈ < j₂₀
                || a₁₈[j₈] == a[j₈])
        && 1 <= i₂₁
        && 0 <= j₂₂
        && (forall i₁₉₆: int, j₁₉₇: int ::
              (  0 <= j₁₉₇
                && j₁₉₇ < j₂₂
                 ==> i₁₉₆ < 100000))
        && i₂₁ < 100000
        && 0 <= j₁₃
        && j₁₃ < j₂₂ + 1
         ==> i₁₉ < 100000
          || i₁₇ < 100000
          || i₁₂ < 100000));

