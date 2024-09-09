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
                        i₄ < 10000
                        && b₁₆[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 0 <= i₁₉
        && 0 <= j₂₀
        && (forall i₁₂₂: int, j₁₂₃: int ::
              (  0 <= i₁₂₂
                && i₁₂₂ < i₁₉
                && 0 <= j₁₂₃
                && j₁₂₃ < j₂₀
                 ==> i₁₂₂ < 10000
                  && a₁₈[j₁₂₃] == b₁₆[i₁₂₂]))
        && (forall i₁₂₄: int, j₁₂₅: int ::
                  0 <= i₁₂₄
                  && i₁₂₄ < i₁₉
                  && 0 <= j₁₂₅
                  && j₁₂₅ < j₂₀
                || a₁₈[j₁₂₅] == a[j₁₂₅])
        && i₁₉ < 10000
        && 0 <= i₇
        && i₇ < i₁₉ + 1
        && 0 <= j₈
        && j₈ < j₂₀ + 1
         ==> i₁₇ < 10000
          || a₁₈[j₂₀ := b₁₆[i₁₉]][j₈] == b₁₆[i₇]));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₇: int, j₈: int ::
      (  0 <= i₁₇
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
        && 0 <= i₁₉
        && 0 <= j₂₀
        && (forall i₁₃₅: int, j₁₃₆: int ::
              (  0 <= i₁₃₅
                && i₁₃₅ < i₁₉
                && 0 <= j₁₃₆
                && j₁₃₆ < j₂₀
                 ==> i₁₃₅ < 10000
                  && a₁₈[j₁₃₆] == b₁₆[i₁₃₅]))
        && (forall i₁₃₇: int, j₁₃₈: int ::
                  0 <= i₁₃₇
                  && i₁₃₇ < i₁₉
                  && 0 <= j₁₃₈
                  && j₁₃₈ < j₂₀
                || a₁₈[j₁₃₈] == a[j₁₃₈])
        && i₁₉ < 10000
         ==> 0 <= i₇
          || i₁₇ < 10000
          || a₁₈[j₂₀ := b₁₆[i₁₉]][j₈] == a[j₈]));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₇: int, j₈: int ::
      (  0 <= i₁₇
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
        && 0 <= i₁₉
        && 0 <= j₂₀
        && (forall i₁₄₈: int, j₁₄₉: int ::
              (  0 <= i₁₄₈
                && i₁₄₈ < i₁₉
                && 0 <= j₁₄₉
                && j₁₄₉ < j₂₀
                 ==> i₁₄₈ < 10000
                  && a₁₈[j₁₄₉] == b₁₆[i₁₄₈]))
        && (forall i₁₅₀: int, j₁₅₁: int ::
                  0 <= i₁₅₀
                  && i₁₅₀ < i₁₉
                  && 0 <= j₁₅₁
                  && j₁₅₁ < j₂₀
                || a₁₈[j₁₅₁] == a[j₁₅₁])
        && i₁₉ < 10000
         ==> i₇ < i₁₉ + 1
          || i₁₇ < 10000
          || a₁₈[j₂₀ := b₁₆[i₁₉]][j₈] == a[j₈]));

goal (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₂₁: int, j₂₂: int ::
      (  0 <= i₁₇
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
        && 0 <= i₁₉
        && 0 <= j₂₀
        && (forall i₇: int, j₈: int ::
              (  0 <= i₇
                && i₇ < i₁₉
                && 0 <= j₈
                && j₈ < j₂₀
                 ==> i₇ < 10000
                  && a₁₈[j₈] == b₁₆[i₇]))
        && (forall i₇: int, j₈: int ::
                  0 <= i₇
                  && i₇ < i₁₉
                  && 0 <= j₈
                  && j₈ < j₂₀
                || a₁₈[j₈] == a[j₈])
        && 0 <= i₂₁
        && 0 <= j₂₂
        && (forall i₁₂: int, j₁₃: int ::
              (  0 <= i₁₂
                && i₁₂ < i₂₁
                && 0 <= j₁₃
                && j₁₃ < j₂₂
                 ==> i₁₂ < 10000))
        && i₂₁ < 10000
         ==> i₁₉ < 10000
          || i₁₇ < 10000
          || a₁₈[j₂₂] == b₁₆[j₂₂]));

