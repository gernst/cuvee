data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall a: [int]int, lim: int, a₁₃: [int]int, k₁₄: int, i₁₅: int ::
      (  0 < lim
        && lim < 1000000 / 1
        && 0 + k₁₄ == i₁₅ + 0
        && 0 <= k₁₄
        && 0 <= i₁₅
        && (forall k₄: int, i₅: int ::
              (  k₄ + k₄ == i₅ + i₅
                && 0 <= k₄
                && k₄ < k₁₄
                && 0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ % 1 == 0
                    && k₄ < lim
                    && i₅ < 1000000
                    && a₁₃[i₅] == i₅ % 1
                  ||   1 + i₅ == 0
                    && (k₄ < lim
                       ==> false)
                    && i₅ < 1000000
                    && a₁₃[i₅] == 1 + i₅
                  ||   (i₅ % 1 == 0
                       ==> false)
                    && k₄ < lim
                    && i₅ < 1000000
                    && a₁₃[i₅] == i₅ % 1
                  ||   (1 + i₅ == 0
                       ==> false)
                    && (k₄ < lim
                       ==> false)
                    && i₅ < 1000000
                    && a₁₃[i₅] == 1 + i₅))
        && (forall k₄: int, i₅: int ::
              (k₄ + k₄ == i₅ + i₅
                 ==> 0 <= k₄
                    && k₄ < k₁₄
                    && 0 <= i₅
                    && i₅ < i₁₅
                  || a₁₃[i₅] == a[i₅]))
        && i₁₅ < 1000000
         ==> a₁₃[i₁₅ := i₁₅ + 1][i₁₅] == 0
          || k₁₄ < lim
          || 0 + k₁₄ == i₁₅ + 1 + 0));

goal {:named "invariant forward"} (forall a: [int]int, lim: int, a₁₃: [int]int, k₁₄: int, i₁₅: int, k₄: int, i₅: int ::
      (  0 < lim
        && lim < 1000000 / 1
        && 0 + k₁₄ == i₁₅ + 0
        && 0 <= k₁₄
        && 0 <= i₁₅
        && (forall k₂₄₂: int, i₂₄₃: int ::
              (  k₂₄₂ + k₂₄₂ == i₂₄₃ + i₂₄₃
                && 0 <= k₂₄₂
                && k₂₄₂ < k₁₄
                && 0 <= i₂₄₃
                && i₂₄₃ < i₁₅
                 ==> i₂₄₃ % 1 == 0
                    && k₂₄₂ < lim
                    && i₂₄₃ < 1000000
                    && a₁₃[i₂₄₃] == i₂₄₃ % 1
                  ||   1 + i₂₄₃ == 0
                    && (k₂₄₂ < lim
                       ==> false)
                    && i₂₄₃ < 1000000
                    && a₁₃[i₂₄₃] == 1 + i₂₄₃
                  ||   (i₂₄₃ % 1 == 0
                       ==> false)
                    && k₂₄₂ < lim
                    && i₂₄₃ < 1000000
                    && a₁₃[i₂₄₃] == i₂₄₃ % 1
                  ||   (1 + i₂₄₃ == 0
                       ==> false)
                    && (k₂₄₂ < lim
                       ==> false)
                    && i₂₄₃ < 1000000
                    && a₁₃[i₂₄₃] == 1 + i₂₄₃))
        && (forall k₂₄₄: int, i₂₄₅: int ::
              (k₂₄₄ + k₂₄₄ == i₂₄₅ + i₂₄₅
                 ==> 0 <= k₂₄₄
                    && k₂₄₄ < k₁₄
                    && 0 <= i₂₄₅
                    && i₂₄₅ < i₁₅
                  || a₁₃[i₂₄₅] == a[i₂₄₅]))
        && i₁₅ < 1000000
        && k₄ + k₄ == i₅ + i₅
         ==> k₄ < k₁₄
          || a₁₃[i₁₅ := i₁₅ + 1][i₁₅] == 0
          || k₁₄ < lim
          || a₁₃[i₁₅ := i₁₅ + 1][i₅] == a[i₅]));

goal {:named "invariant forward"} (forall a: [int]int, lim: int, a₁₃: [int]int, k₁₄: int, i₁₅: int, j₁₆: int, i₁₇: int ::
      (  0 < lim
        && lim < 1000000 / 1
        && 0 + k₁₄ == i₁₅ + 0
        && 0 <= k₁₄
        && 0 <= i₁₅
        && (forall k₄: int, i₅: int ::
              (  k₄ + k₄ == i₅ + i₅
                && 0 <= k₄
                && k₄ < k₁₄
                && 0 <= i₅
                && i₅ < i₁₅
                 ==> i₅ % 1 == 0
                    && k₄ < lim
                    && i₅ < 1000000
                    && a₁₃[i₅] == i₅ % 1
                  ||   1 + i₅ == 0
                    && (k₄ < lim
                       ==> false)
                    && i₅ < 1000000
                    && a₁₃[i₅] == 1 + i₅
                  ||   (i₅ % 1 == 0
                       ==> false)
                    && k₄ < lim
                    && i₅ < 1000000
                    && a₁₃[i₅] == i₅ % 1
                  ||   (1 + i₅ == 0
                       ==> false)
                    && (k₄ < lim
                       ==> false)
                    && i₅ < 1000000
                    && a₁₃[i₅] == 1 + i₅))
        && (forall k₄: int, i₅: int ::
              (k₄ + k₄ == i₅ + i₅
                 ==> 0 <= k₄
                    && k₄ < k₁₄
                    && 0 <= i₅
                    && i₅ < i₁₅
                  || a₁₃[i₅] == a[i₅]))
        && j₁₆ + 0 == i₁₇ + 0
        && 0 <= j₁₆
        && 0 <= i₁₇
        && (forall j₉: int, i₁₀: int ::
              (  j₉ + j₉ == i₁₀ + i₁₀
                && 0 <= j₉
                && j₉ < j₁₆
                && 0 <= i₁₀
                && i₁₀ < i₁₇
                 ==> a₁₃[i₁₀] == 0
                    && i₁₀ < 1000000
                  ||   (a₁₃[i₁₀] == 0
                       ==> false)
                    && i₁₀ < 1000000))
        && i₁₇ < 1000000
         ==> a₁₃[i₁₇] == 0
          || i₁₅ < 1000000
          || j₁₆ + 0 == i₁₇ + 1 + 0));

