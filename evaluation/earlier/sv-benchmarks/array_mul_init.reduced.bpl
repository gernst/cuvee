data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, a₁₉: [int]int, b₂₀: [int]int, i₂₁: int, a₂₃: [int]int, b₂₄: [int]int, i₂₅: int, i₂₆: int ::
      (  0 <= i₂₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₁
                 ==> i₅ < 100000
                  && a₁₉[i₅] == i₅
                  && b₂₀[i₅] == i₅))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₁
                ||   a₁₉[i₅] == a[i₅]
                  && b₂₀[i₅] == b[i₅])
        && 0 <= i₂₅
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₂₅
                 ==> (exists __VERIFIER_nondet_short₂₉: int, k₁₀: int ::
                          (__VERIFIER_nondet_short₂₉ == 0
                             ==> false)
                          && i₁₂ < 100000
                          && a₂₃[i₁₂] == k₁₀
                          && b₂₄[i₁₂] == k₁₀ * k₁₀)
                  || (exists __VERIFIER_nondet_short₂₉: int ::
                          __VERIFIER_nondet_short₂₉ == 0
                          && i₁₂ < 100000)))
        && (forall i₁₂: int ::
                  0 <= i₁₂
                  && i₁₂ < i₂₅
                ||   a₂₃[i₁₂] == a₁₉[i₁₂]
                  && b₂₄[i₁₂] == b₂₀[i₁₂])
        && 0 <= i₂₆
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₂₆
                 ==> i₁₇ < 100000))
        && i₂₆ < 100000
         ==> i₂₅ < 100000
          || i₂₁ < 100000
          || a₂₃[i₂₆] == b₂₄[i₂₆]
          || b₂₄[i₂₆] == a₂₃[i₂₆] * a₂₃[i₂₆]));

