data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall password: [int]int, guess: [int]int, password₁₇: [int]int, guess₁₈: [int]int, i₁₉: int, result₂₀: int, i₂₁: int, x₂₂: int ::
      (  0 <= i₁₉
        && i₁₉ <= 100000
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₁₉
                 ==> (exists __VERIFIER_nondet_int₁₄: int, __VERIFIER_nondet_int₂₅: int ::
                        i₆ < 100000
                        && password₁₇[i₆] == __VERIFIER_nondet_int₁₄
                        && guess₁₈[i₆] == __VERIFIER_nondet_int₂₅)))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₁₉
                ||   password₁₇[i₆] == password[i₆]
                  && guess₁₈[i₆] == guess[i₆])
        && 0 <= i₂₁
        && i₂₁ <= 100000
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₁
                 ==> (password₁₇[i₁₁] == guess₁₈[i₁₁]
                       ==> false)
                    && i₁₁ < 100000
                  ||   password₁₇[i₁₁] == guess₁₈[i₁₁]
                    && i₁₁ < 100000))
        && 0 <= x₂₂
        && x₂₂ <= 100000
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₂₂
                 ==> x₁₅ < 100000))
        && x₂₂ < 100000
         ==> result₂₀ == 0
          || i₂₁ < 100000
          || i₁₉ < 100000
          || password₁₇[x₂₂] == guess₁₈[x₂₂]));

