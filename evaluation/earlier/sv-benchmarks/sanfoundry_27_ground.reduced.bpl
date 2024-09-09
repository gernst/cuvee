data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall array: [int]int, array₁₄: [int]int, i₁₅: int, largest₁₆: int, i₁₇: int, x₁₈: int ::
      (  0 <= i₁₅
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₅
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 100000
                        && array₁₄[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₅
                || array₁₄[i₄] == array[i₄])
        && 1 <= i₁₇
        && (forall largest₇: int, i₈: int ::
              (  1 <= i₈
                && i₈ < i₁₇
                 ==> largest₇ < array₁₄[i₈]
                    && i₈ < 100000
                  ||   (largest₇ < array₁₄[i₈]
                       ==> false)
                    && i₈ < 100000))
        && 0 <= x₁₈
        && (forall x₁₂: int ::
              (  0 <= x₁₂
                && x₁₂ < x₁₈
                 ==> x₁₂ < 100000))
        && x₁₈ < 100000
         ==> i₁₇ < 100000
          || i₁₅ < 100000
          || array₁₄[x₁₈] <= largest₁₆));

