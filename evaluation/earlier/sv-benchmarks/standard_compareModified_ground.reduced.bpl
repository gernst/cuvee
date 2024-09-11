data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall a: [int]int, b: [int]int, c: [int]int, a₂₁: [int]int, b₂₂: [int]int, j₂₃: int, rv₂₄: int, c₂₅: [int]int, i₂₆: int, x₂₇: int ::
      (  0 <= j₂₃
        && (forall j₆: int ::
              (  0 <= j₆
                && j₆ < j₂₃
                 ==> (exists nondet_int₁₄: int, nondet_int₂₅: int ::
                        j₆ < 100000
                        && a₂₁[j₆] == nondet_int₁₄
                        && b₂₂[j₆] == nondet_int₂₅)))
        && (forall j₆: int ::
                  0 <= j₆
                  && j₆ < j₂₃
                ||   a₂₁[j₆] == a[j₆]
                  && b₂₂[j₆] == b[j₆])
        && 0 <= i₂₆
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₆
                 ==> (a₂₁[i₁₁] == b₂₂[i₁₁]
                       ==> false)
                    && i₁₁ < 100000
                    && c₂₅[i₁₁] == a₂₁[i₁₁]
                  ||   a₂₁[i₁₁] == b₂₂[i₁₁]
                    && i₁₁ < 100000
                    && c₂₅[i₁₁] == a₂₁[i₁₁]))
        && (forall i₁₁: int ::
                  0 <= i₁₁
                  && i₁₁ < i₂₆
                || c₂₅[i₁₁] == c[i₁₁])
        && 0 <= x₂₇
        && (forall x₁₆: int ::
              (  0 <= x₁₆
                && x₁₆ < x₂₇
                 ==> x₁₆ < 100000))
        && x₂₇ < 100000
         ==> rv₂₄ == 0
          || i₂₆ < 100000
          || j₂₃ < 100000
          || a₂₁[x₂₇] == b₂₂[x₂₇]));

