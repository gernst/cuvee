data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₇: int, j₈: int ::
      (  0 <= i₁₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists nondet_int₁₃: int ::
                        -2147483648 <= nondet_int₁₃
                        && nondet_int₁₃ < 2147483648
                        && i₄ < 100000
                        && b₁₆[i₄] == nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 1 <= i₁₉
        && 0 <= j₂₀
        && (forall i₁₀₅: int, j₁₀₆: int ::
              (  0 <= j₁₀₆
                && j₁₀₆ < j₂₀
                 ==> i₁₀₅ < 100000
                  && a₁₈[j₁₀₆] == b₁₆[i₁₀₅]))
        && (forall j₁₀₇: int ::
                  0 <= j₁₀₇
                  && j₁₀₇ < j₂₀
                || a₁₈[j₁₀₇] == a[j₁₀₇])
        && i₁₉ < 100000
        && 0 <= j₈
        && j₈ < j₂₀ + 1
         ==> i₁₇ < 100000
          || i₇ < 100000));

goal {:named "invariant forward"} (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₇: int, j₈: int ::
      (  0 <= i₁₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists nondet_int₁₃: int ::
                        -2147483648 <= nondet_int₁₃
                        && nondet_int₁₃ < 2147483648
                        && i₄ < 100000
                        && b₁₆[i₄] == nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₇
                || b₁₆[i₄] == b[i₄])
        && 1 <= i₁₉
        && 0 <= j₂₀
        && (forall i₁₁₇: int, j₁₁₈: int ::
              (  0 <= j₁₁₈
                && j₁₁₈ < j₂₀
                 ==> i₁₁₇ < 100000
                  && a₁₈[j₁₁₈] == b₁₆[i₁₁₇]))
        && (forall j₁₁₉: int ::
                  0 <= j₁₁₉
                  && j₁₁₉ < j₂₀
                || a₁₈[j₁₁₉] == a[j₁₁₉])
        && i₁₉ < 100000
        && 0 <= j₈
        && j₈ < j₂₀ + 1
         ==> i₁₇ < 100000
          || a₁₈[j₂₀ := b₁₆[i₁₉]][j₈] == b₁₆[i₇]));

goal {:named "assert"} (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₂₁: int, j₂₂: int ::
      (  0 <= i₁₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists nondet_int₁₃: int ::
                        -2147483648 <= nondet_int₁₃
                        && nondet_int₁₃ < 2147483648
                        && i₄ < 100000
                        && b₁₆[i₄] == nondet_int₁₃)))
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
          || a₁₈[j₂₂] == b₁₆[2 * j₂₂ + 1]));

goal {:named "invariant forward"} (forall a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, j₂₀: int, i₂₁: int, j₂₂: int, i₁₂: int, j₁₃: int ::
      (  0 <= i₁₇
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₇
                 ==> (exists nondet_int₁₃: int ::
                        -2147483648 <= nondet_int₁₃
                        && nondet_int₁₃ < 2147483648
                        && i₄ < 100000
                        && b₁₆[i₄] == nondet_int₁₃)))
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
        && (forall i₁₉₇: int, j₁₉₈: int ::
              (  0 <= j₁₉₈
                && j₁₉₈ < j₂₂
                 ==> i₁₉₇ < 100000))
        && i₂₁ < 100000
        && 0 <= j₁₃
        && j₁₃ < j₂₂ + 1
         ==> i₁₉ < 100000
          || i₁₇ < 100000
          || i₁₂ < 100000));

