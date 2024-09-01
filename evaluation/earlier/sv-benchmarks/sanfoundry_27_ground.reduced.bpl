data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall array: [int]int, array₁₅: [int]int, i₁₆: int, largest₁₇: int, i₁₈: int, x₁₉: int ::
      (  0 <= i₁₆
        && i₁₆ <= 100000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < i₁₆
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₆
                        && array₁₅[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₆)
                || array₁₅[x₅] == array[x₅])
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₁₆
                 ==> i₄ < 100000))
        && 1 <= i₁₈
        && i₁₈ <= 100000
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 1 <= i₉
                && i₉ < i₁₈
                 ==> i₉ < 100000))
        && 0 <= x₁₉
        && x₁₉ <= 100000
        && (forall x₁₃: int ::
              (  x₁₃ <= x₁₃
                && 0 <= x₁₃
                && x₁₃ < x₁₉
                 ==> x₁₃ < 100000))
        && x₁₉ < 100000
         ==> i₁₈ < 100000
          || i₁₆ < 100000
          || array₁₅[x₁₉] <= largest₁₇));

