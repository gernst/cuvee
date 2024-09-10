data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall j: int, N: int, a: [int]int, b: [int]int, j₁₇: int, i₁₈: int, b₁₉: [int]int, i₂₀: int, k₂₁: int, i₂₂: int ::
      (  j < 10000
        && -10000 < j
        && N < 10000
        && -10000 < N
        && 0 <= i₁₈
        && (forall j₆: int, i₇: int ::
              (  0 <= i₇
                && i₇ < i₁₈
                 ==> a[i₇] < j₆
                    && a[i₇] < 10000
                    && -10000 < a[i₇]
                    && i₇ < N
                  ||   (a[i₇] < j₆
                       ==> false)
                    && a[i₇] < 10000
                    && -10000 < a[i₇]
                    && i₇ < N))
        && 0 <= i₂₀
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₀
                 ==> i₁₀ < N
                  && b₁₉[i₁₀] == -j₁₇ + a[i₁₀]))
        && (forall i₁₀: int ::
                  0 <= i₁₀
                  && i₁₀ < i₂₀
                || b₁₉[i₁₀] == b[i₁₀])
        && 0 <= i₂₂
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₂₂
                 ==> i₁₄ < N))
         ==> i₂₂ < N
          || i₂₀ < N
          || i₁₈ < N
          || 0 <= k₂₁));

