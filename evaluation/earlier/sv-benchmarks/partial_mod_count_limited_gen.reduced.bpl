data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall a: [int]int, lim: int, R: int, a₁₄: [int]int, k₁₅: int, i₁₆: int ::
      (  1 < R
        && R < 6
        && 0 < lim
        && lim < 1000 / R
        && 0 + k₁₅ == i₁₆ + 0
        && 0 <= k₁₅
        && 0 <= i₁₆
        && (forall k₅: int, i₆: int ::
              (  k₅ + k₅ == i₆ + i₆
                && 0 <= k₅
                && k₅ < k₁₅
                && 0 <= i₆
                && i₆ < i₁₆
                 ==> i₆ % R == 0
                    && 1000 / R < i₆
                    && k₅ < lim
                    && i₆ < 1000
                    && a₁₄[i₆] == i₆ % R
                  ||   1 + i₆ == 0
                    && (  1000 / R < i₆
                      && k₅ < lim
                       ==> false)
                    && i₆ < 1000
                    && a₁₄[i₆] == 1 + i₆
                  ||   (i₆ % R == 0
                       ==> false)
                    && 1000 / R < i₆
                    && k₅ < lim
                    && i₆ < 1000
                    && a₁₄[i₆] == i₆ % R
                  ||   (1 + i₆ == 0
                       ==> false)
                    && (  1000 / R < i₆
                      && k₅ < lim
                       ==> false)
                    && i₆ < 1000
                    && a₁₄[i₆] == 1 + i₆))
        && (forall k₅: int, i₆: int ::
              (k₅ + k₅ == i₆ + i₆
                 ==> 0 <= k₅
                    && k₅ < k₁₅
                    && 0 <= i₆
                    && i₆ < i₁₆
                  || a₁₄[i₆] == a[i₆]))
        && i₁₆ < 1000
         ==> a₁₄[i₁₆ := i₁₆ + 1][i₁₆] == 0
          || 1000 / R < i₁₆
          || 0 + k₁₅ == i₁₆ + 1 + 0));

goal {:named "invariant forward"} (forall a: [int]int, lim: int, R: int, a₁₄: [int]int, k₁₅: int, i₁₆: int, k₅: int, i₆: int ::
      (  1 < R
        && R < 6
        && 0 < lim
        && lim < 1000 / R
        && 0 + k₁₅ == i₁₆ + 0
        && 0 <= k₁₅
        && 0 <= i₁₆
        && (forall k₂₈₀: int, i₂₈₁: int ::
              (  k₂₈₀ + k₂₈₀ == i₂₈₁ + i₂₈₁
                && 0 <= k₂₈₀
                && k₂₈₀ < k₁₅
                && 0 <= i₂₈₁
                && i₂₈₁ < i₁₆
                 ==> i₂₈₁ % R == 0
                    && 1000 / R < i₂₈₁
                    && k₂₈₀ < lim
                    && i₂₈₁ < 1000
                    && a₁₄[i₂₈₁] == i₂₈₁ % R
                  ||   1 + i₂₈₁ == 0
                    && (  1000 / R < i₂₈₁
                      && k₂₈₀ < lim
                       ==> false)
                    && i₂₈₁ < 1000
                    && a₁₄[i₂₈₁] == 1 + i₂₈₁
                  ||   (i₂₈₁ % R == 0
                       ==> false)
                    && 1000 / R < i₂₈₁
                    && k₂₈₀ < lim
                    && i₂₈₁ < 1000
                    && a₁₄[i₂₈₁] == i₂₈₁ % R
                  ||   (1 + i₂₈₁ == 0
                       ==> false)
                    && (  1000 / R < i₂₈₁
                      && k₂₈₀ < lim
                       ==> false)
                    && i₂₈₁ < 1000
                    && a₁₄[i₂₈₁] == 1 + i₂₈₁))
        && (forall k₂₈₂: int, i₂₈₃: int ::
              (k₂₈₂ + k₂₈₂ == i₂₈₃ + i₂₈₃
                 ==> 0 <= k₂₈₂
                    && k₂₈₂ < k₁₅
                    && 0 <= i₂₈₃
                    && i₂₈₃ < i₁₆
                  || a₁₄[i₂₈₃] == a[i₂₈₃]))
        && i₁₆ < 1000
        && k₅ + k₅ == i₆ + i₆
         ==> k₅ < k₁₅
          || a₁₄[i₁₆ := i₁₆ + 1][i₁₆] == 0
          || 1000 / R < i₁₆
          || a₁₄[i₁₆ := i₁₆ + 1][i₆] == a[i₆]));

goal {:named "invariant forward"} (forall a: [int]int, lim: int, R: int, a₁₄: [int]int, k₁₅: int, i₁₆: int, k₅: int, i₆: int ::
      (  1 < R
        && R < 6
        && 0 < lim
        && lim < 1000 / R
        && 0 + k₁₅ == i₁₆ + 0
        && 0 <= k₁₅
        && 0 <= i₁₆
        && (forall k₂₉₂: int, i₂₉₃: int ::
              (  k₂₉₂ + k₂₉₂ == i₂₉₃ + i₂₉₃
                && 0 <= k₂₉₂
                && k₂₉₂ < k₁₅
                && 0 <= i₂₉₃
                && i₂₉₃ < i₁₆
                 ==> i₂₉₃ % R == 0
                    && 1000 / R < i₂₉₃
                    && k₂₉₂ < lim
                    && i₂₉₃ < 1000
                    && a₁₄[i₂₉₃] == i₂₉₃ % R
                  ||   1 + i₂₉₃ == 0
                    && (  1000 / R < i₂₉₃
                      && k₂₉₂ < lim
                       ==> false)
                    && i₂₉₃ < 1000
                    && a₁₄[i₂₉₃] == 1 + i₂₉₃
                  ||   (i₂₉₃ % R == 0
                       ==> false)
                    && 1000 / R < i₂₉₃
                    && k₂₉₂ < lim
                    && i₂₉₃ < 1000
                    && a₁₄[i₂₉₃] == i₂₉₃ % R
                  ||   (1 + i₂₉₃ == 0
                       ==> false)
                    && (  1000 / R < i₂₉₃
                      && k₂₉₂ < lim
                       ==> false)
                    && i₂₉₃ < 1000
                    && a₁₄[i₂₉₃] == 1 + i₂₉₃))
        && (forall k₂₉₄: int, i₂₉₅: int ::
              (k₂₉₄ + k₂₉₄ == i₂₉₅ + i₂₉₅
                 ==> 0 <= k₂₉₄
                    && k₂₉₄ < k₁₅
                    && 0 <= i₂₉₅
                    && i₂₉₅ < i₁₆
                  || a₁₄[i₂₉₅] == a[i₂₉₅]))
        && i₁₆ < 1000
        && k₅ + k₅ == i₆ + i₆
         ==> 0 <= i₆
          || a₁₄[i₁₆ := i₁₆ + 1][i₁₆] == 0
          || 1000 / R < i₁₆
          || a₁₄[i₁₆ := i₁₆ + 1][i₆] == a[i₆]));

goal {:named "invariant forward"} (forall a: [int]int, lim: int, R: int, a₁₄: [int]int, k₁₅: int, i₁₆: int ::
      (  1 < R
        && R < 6
        && 0 < lim
        && lim < 1000 / R
        && 0 + k₁₅ == i₁₆ + 0
        && 0 <= k₁₅
        && 0 <= i₁₆
        && (forall k₅: int, i₆: int ::
              (  k₅ + k₅ == i₆ + i₆
                && 0 <= k₅
                && k₅ < k₁₅
                && 0 <= i₆
                && i₆ < i₁₆
                 ==> i₆ % R == 0
                    && 1000 / R < i₆
                    && k₅ < lim
                    && i₆ < 1000
                    && a₁₄[i₆] == i₆ % R
                  ||   1 + i₆ == 0
                    && (  1000 / R < i₆
                      && k₅ < lim
                       ==> false)
                    && i₆ < 1000
                    && a₁₄[i₆] == 1 + i₆
                  ||   (i₆ % R == 0
                       ==> false)
                    && 1000 / R < i₆
                    && k₅ < lim
                    && i₆ < 1000
                    && a₁₄[i₆] == i₆ % R
                  ||   (1 + i₆ == 0
                       ==> false)
                    && (  1000 / R < i₆
                      && k₅ < lim
                       ==> false)
                    && i₆ < 1000
                    && a₁₄[i₆] == 1 + i₆))
        && (forall k₅: int, i₆: int ::
              (k₅ + k₅ == i₆ + i₆
                 ==> 0 <= k₅
                    && k₅ < k₁₅
                    && 0 <= i₆
                    && i₆ < i₁₆
                  || a₁₄[i₆] == a[i₆]))
        && i₁₆ < 1000
         ==> a₁₄[i₁₆ := i₁₆ + 1][i₁₆] == 0
          || k₁₅ < lim
          || 0 + k₁₅ == i₁₆ + 1 + 0));

goal {:named "invariant forward"} (forall a: [int]int, lim: int, R: int, a₁₄: [int]int, k₁₅: int, i₁₆: int, k₅: int, i₆: int ::
      (  1 < R
        && R < 6
        && 0 < lim
        && lim < 1000 / R
        && 0 + k₁₅ == i₁₆ + 0
        && 0 <= k₁₅
        && 0 <= i₁₆
        && (forall k₄₀₄: int, i₄₀₅: int ::
              (  k₄₀₄ + k₄₀₄ == i₄₀₅ + i₄₀₅
                && 0 <= k₄₀₄
                && k₄₀₄ < k₁₅
                && 0 <= i₄₀₅
                && i₄₀₅ < i₁₆
                 ==> i₄₀₅ % R == 0
                    && 1000 / R < i₄₀₅
                    && k₄₀₄ < lim
                    && i₄₀₅ < 1000
                    && a₁₄[i₄₀₅] == i₄₀₅ % R
                  ||   1 + i₄₀₅ == 0
                    && (  1000 / R < i₄₀₅
                      && k₄₀₄ < lim
                       ==> false)
                    && i₄₀₅ < 1000
                    && a₁₄[i₄₀₅] == 1 + i₄₀₅
                  ||   (i₄₀₅ % R == 0
                       ==> false)
                    && 1000 / R < i₄₀₅
                    && k₄₀₄ < lim
                    && i₄₀₅ < 1000
                    && a₁₄[i₄₀₅] == i₄₀₅ % R
                  ||   (1 + i₄₀₅ == 0
                       ==> false)
                    && (  1000 / R < i₄₀₅
                      && k₄₀₄ < lim
                       ==> false)
                    && i₄₀₅ < 1000
                    && a₁₄[i₄₀₅] == 1 + i₄₀₅))
        && (forall k₄₀₆: int, i₄₀₇: int ::
              (k₄₀₆ + k₄₀₆ == i₄₀₇ + i₄₀₇
                 ==> 0 <= k₄₀₆
                    && k₄₀₆ < k₁₅
                    && 0 <= i₄₀₇
                    && i₄₀₇ < i₁₆
                  || a₁₄[i₄₀₇] == a[i₄₀₇]))
        && i₁₆ < 1000
        && k₅ + k₅ == i₆ + i₆
         ==> k₅ < k₁₅
          || a₁₄[i₁₆ := i₁₆ + 1][i₁₆] == 0
          || k₁₅ < lim
          || a₁₄[i₁₆ := i₁₆ + 1][i₆] == a[i₆]));

goal {:named "invariant forward"} (forall a: [int]int, lim: int, R: int, a₁₄: [int]int, k₁₅: int, i₁₆: int, j₁₇: int, i₁₈: int ::
      (  1 < R
        && R < 6
        && 0 < lim
        && lim < 1000 / R
        && 0 + k₁₅ == i₁₆ + 0
        && 0 <= k₁₅
        && 0 <= i₁₆
        && (forall k₅: int, i₆: int ::
              (  k₅ + k₅ == i₆ + i₆
                && 0 <= k₅
                && k₅ < k₁₅
                && 0 <= i₆
                && i₆ < i₁₆
                 ==> i₆ % R == 0
                    && 1000 / R < i₆
                    && k₅ < lim
                    && i₆ < 1000
                    && a₁₄[i₆] == i₆ % R
                  ||   1 + i₆ == 0
                    && (  1000 / R < i₆
                      && k₅ < lim
                       ==> false)
                    && i₆ < 1000
                    && a₁₄[i₆] == 1 + i₆
                  ||   (i₆ % R == 0
                       ==> false)
                    && 1000 / R < i₆
                    && k₅ < lim
                    && i₆ < 1000
                    && a₁₄[i₆] == i₆ % R
                  ||   (1 + i₆ == 0
                       ==> false)
                    && (  1000 / R < i₆
                      && k₅ < lim
                       ==> false)
                    && i₆ < 1000
                    && a₁₄[i₆] == 1 + i₆))
        && (forall k₅: int, i₆: int ::
              (k₅ + k₅ == i₆ + i₆
                 ==> 0 <= k₅
                    && k₅ < k₁₅
                    && 0 <= i₆
                    && i₆ < i₁₆
                  || a₁₄[i₆] == a[i₆]))
        && j₁₇ + 0 == i₁₈ + 0
        && 0 <= j₁₇
        && 0 <= i₁₈
        && (forall j₁₀: int, i₁₁: int ::
              (  j₁₀ + j₁₀ == i₁₁ + i₁₁
                && 0 <= j₁₀
                && j₁₀ < j₁₇
                && 0 <= i₁₁
                && i₁₁ < i₁₈
                 ==> a₁₄[i₁₁] == 0
                    && i₁₁ < 1000
                  ||   (a₁₄[i₁₁] == 0
                       ==> false)
                    && i₁₁ < 1000))
        && i₁₈ < 1000
         ==> a₁₄[i₁₈] == 0
          || i₁₆ < 1000
          || j₁₇ + 0 == i₁₈ + 1 + 0));

