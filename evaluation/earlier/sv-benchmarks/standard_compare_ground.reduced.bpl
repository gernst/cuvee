data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall a: [int]int, b: [int]int, a₁₆: [int]int, b₁₇: [int]int, j₁₈: int, rv₁₉: int, i₂₀: int, x₂₁: int ::
      (  0 <= j₁₈
        && (forall j₅: int ::
              (  0 <= j₅
                && j₅ < j₁₈
                 ==> (exists __VERIFIER_nondet_int₁₃: int, __VERIFIER_nondet_int₂₄: int ::
                        j₅ < 100000
                        && a₁₆[j₅] == __VERIFIER_nondet_int₁₃
                        && b₁₇[j₅] == __VERIFIER_nondet_int₂₄)))
        && (forall j₅: int ::
                  0 <= j₅
                  && j₅ < j₁₈
                ||   a₁₆[j₅] == a[j₅]
                  && b₁₇[j₅] == b[j₅])
        && 0 <= i₂₀
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₀
                 ==> (a₁₆[i₁₀] == b₁₇[i₁₀]
                       ==> false)
                    && i₁₀ < 100000
                  ||   a₁₆[i₁₀] == b₁₇[i₁₀]
                    && i₁₀ < 100000))
        && 0 <= x₂₁
        && (forall x₁₄: int ::
              (  0 <= x₁₄
                && x₁₄ < x₂₁
                 ==> x₁₄ < 100000))
        && x₂₁ < 100000
         ==> rv₁₉ == 0
          || i₂₀ < 100000
          || j₁₈ < 100000
          || a₁₆[x₂₁] == b₁₇[x₂₁]));

