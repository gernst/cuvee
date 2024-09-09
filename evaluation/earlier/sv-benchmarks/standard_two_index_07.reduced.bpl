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
        && 0 <= j₂₀
        && (forall i₉₄: int, j₉₅: int ::
              (  0 <= j₉₅
                && j₉₅ < j₂₀
                 ==> i₉₄ < 100000
                  && a₁₈[j₉₅] == b₁₆[i₉₄]))
        && (forall j₉₆: int ::
                  0 <= j₉₆
                  && j₉₆ < j₂₀
                || a₁₈[j₉₆] == a[j₉₆])
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
        && 0 <= j₂₀
        && (forall i₁₀₆: int, j₁₀₇: int ::
              (  0 <= j₁₀₇
                && j₁₀₇ < j₂₀
                 ==> i₁₀₆ < 100000
                  && a₁₈[j₁₀₇] == b₁₆[i₁₀₆]))
        && (forall j₁₀₈: int ::
                  0 <= j₁₀₈
                  && j₁₀₈ < j₂₀
                || a₁₈[j₁₀₈] == a[j₁₀₈])
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
        && 0 <= j₂₂
        && (forall i₁₂: int, j₁₃: int ::
              (  0 <= j₁₃
                && j₁₃ < j₂₂
                 ==> i₁₂ < 100000))
        && i₂₁ < 100000
         ==> i₁₉ < 100000
          || i₁₇ < 100000
          || a₁₈[j₂₂] == b₁₆[7 * j₂₂ + 1]));

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
        && 0 <= j₂₂
        && (forall i₁₇₀: int, j₁₇₁: int ::
              (  0 <= j₁₇₁
                && j₁₇₁ < j₂₂
                 ==> i₁₇₀ < 100000))
        && i₂₁ < 100000
        && 0 <= j₁₃
        && j₁₃ < j₂₂ + 1
         ==> i₁₉ < 100000
          || i₁₇ < 100000
          || i₁₂ < 100000));

