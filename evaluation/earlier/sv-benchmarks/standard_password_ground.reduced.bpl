data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall password: [int]int, guess: [int]int, password₁₉: [int]int, guess₂₀: [int]int, i₂₁: int, result₂₂: int, i₂₃: int, x₂₄: int ::
      (  0 <= i₂₁
        && i₂₁ <= 100000
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₁
                 ==> (exists __VERIFIER_nondet_int₁₄: int, i₆: int ::
                        i₆ < 100000
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₁
                        && password₁₉[x₇] == __VERIFIER_nondet_int₁₄)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₁)
                || password₁₉[x₇] == password[x₇])
        && (forall x₈: int, i₆: int ::
              (  x₈ == i₆
                && 0 <= i₆
                && i₆ < i₂₁
                 ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                        i₆ < 100000
                        && x₈ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₁
                        && guess₂₀[x₈] == __VERIFIER_nondet_int₂₅)))
        && (forall x₈: int ::
                (exists i₆: int ::
                        x₈ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₁)
                || guess₂₀[x₈] == guess[x₈])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₂₁
                 ==> i₆ < 100000))
        && 0 <= i₂₃
        && i₂₃ <= 100000
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₃
                 ==> i₁₃ < 100000))
        && 0 <= x₂₄
        && x₂₄ <= 100000
        && (forall x₁₇: int ::
              (  x₁₇ <= x₁₇
                && 0 <= x₁₇
                && x₁₇ < x₂₄
                 ==> x₁₇ < 100000))
        && x₂₄ < 100000
         ==> result₂₂ == 0
          || i₂₃ < 100000
          || i₂₁ < 100000
          || password₁₉[x₂₄] == guess₂₀[x₂₄]));

