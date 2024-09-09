data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall a: [int]int, a₁₃: [int]int, j₁₄: int, max₁₅: int, i₁₆: int, x₁₇: int ::
      (  0 <= j₁₄
        && (forall j₃: int ::
              (  0 <= j₃
                && j₃ < j₁₄
                 ==> (exists __VERIFIER_nondet_int₁₂: int ::
                        j₃ < 100000
                        && a₁₃[j₃] == __VERIFIER_nondet_int₁₂)))
        && (forall j₃: int ::
                  0 <= j₃
                  && j₃ < j₁₄
                || a₁₃[j₃] == a[j₃])
        && 0 <= i₁₆
        && (forall max₆: int, i₇: int ::
              (  0 <= i₇
                && i₇ < i₁₆
                 ==> max₆ < a₁₃[i₇]
                    && i₇ < 100000
                  ||   (max₆ < a₁₃[i₇]
                       ==> false)
                    && i₇ < 100000))
        && 0 <= x₁₇
        && (forall x₁₁: int ::
              (  0 <= x₁₁
                && x₁₁ < x₁₇
                 ==> x₁₁ < 100000))
        && x₁₇ < 100000
         ==> i₁₆ < 100000
          || j₁₄ < 100000
          || a₁₃[x₁₇] <= max₁₅));

