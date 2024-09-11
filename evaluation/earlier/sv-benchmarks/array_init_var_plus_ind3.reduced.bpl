data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall a: [int]int, a₁₁: [int]int, j₁₂: int, i₁₃: int, x: int, j₄: int, i₅: int ::
      (  0 <= i₁₃
        && (forall j₆₆: int, i₆₇: int ::
              (  0 <= i₆₇
                && i₆₇ < i₁₃
                 ==> (exists x₃: int ::
                        x₃ == 0
                        && i₆₇ < 100000
                        && a₁₁[i₆₇] == j₆₆)))
        && (forall i₆₈: int ::
                  0 <= i₆₈
                  && i₆₈ < i₁₃
                || a₁₁[i₆₈] == a[i₆₈])
        && (forall i₆₉: int, x₃: int ::
              (  0 <= i₆₉
                && i₆₉ < i₁₃
                && i₆₉ < 100000
                 ==> x₃ == 0))
        && i₁₃ < 100000
        && x == 0
        && 0 <= i₅
        && i₅ < i₁₃ + 1
         ==> (exists x₃: int ::
                x₃ == 0
                && i₅ < 100000
                && a₁₁[i₁₃ := j₁₂][i₅] == j₄)));

goal {:named "invariant forward"} (forall a: [int]int, a₁₁: [int]int, i₁₃: int, x: int, i₅: int, x₃: int ::
      (  0 <= i₁₃
        && (forall j₄: int, i₈₈: int ::
              (  0 <= i₈₈
                && i₈₈ < i₁₃
                 ==> (exists x₈₉: int ::
                        x₈₉ == 0
                        && i₈₈ < 100000
                        && a₁₁[i₈₈] == j₄)))
        && (forall i₉₀: int ::
                  0 <= i₉₀
                  && i₉₀ < i₁₃
                || a₁₁[i₉₀] == a[i₉₀])
        && (forall i₉₂: int, x₉₁: int ::
              (  0 <= i₉₂
                && i₉₂ < i₁₃
                && i₉₂ < 100000
                 ==> x₉₁ == 0))
        && i₁₃ < 100000
        && x == 0
        && 0 <= i₅
        && i₅ < i₁₃ + 1
        && i₅ < 100000
         ==> x₃ == 0));

