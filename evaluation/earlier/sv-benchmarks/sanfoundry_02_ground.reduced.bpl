data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall array: [int]int, array₂₇: [int]int, i₂₈: int, largest1₃₀: int, i₃₁: int, x₃₂: int ::
      (  0 <= i₂₈
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₈
                 ==> (exists nondet_int₁₆: int ::
                        i₇ < 100000
                        && array₂₇[i₇] == nondet_int₁₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₈
                || array₂₇[i₇] == array[i₇])
        && array₂₇[0] < array₂₇[1]
        && 2 <= i₃₁
        && (forall largest2₁₀: int, largest1₁₁: int, i₁₂: int ::
              (  2 <= i₁₂
                && i₁₂ < i₃₁
                 ==> largest1₁₁ <= array₂₇[i₁₂]
                    && i₁₂ < 100000
                  ||   largest2₁₀ < array₂₇[i₁₂]
                    && (largest1₁₁ <= array₂₇[i₁₂]
                       ==> false)
                    && i₁₂ < 100000
                  ||   (largest2₁₀ < array₂₇[i₁₂]
                       ==> false)
                    && (largest1₁₁ <= array₂₇[i₁₂]
                       ==> false)
                    && i₁₂ < 100000))
        && 0 <= x₃₂
        && (forall x₂₁: int ::
              (  0 <= x₂₁
                && x₂₁ < x₃₂
                 ==> x₂₁ < 100000))
        && x₃₂ < 100000
         ==> i₃₁ < 100000
          || i₂₈ < 100000
          || array₂₇[x₃₂] <= largest1₃₀));

goal {:named "assert"} (forall array: [int]int, array₂₇: [int]int, i₂₈: int, largest2₂₉: int, largest1₃₀: int, i₃₁: int, x₃₂: int, x₃₃: int ::
      (  0 <= i₂₈
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₈
                 ==> (exists nondet_int₁₆: int ::
                        i₇ < 100000
                        && array₂₇[i₇] == nondet_int₁₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₈
                || array₂₇[i₇] == array[i₇])
        && array₂₇[0] < array₂₇[1]
        && 2 <= i₃₁
        && (forall largest2₁₀: int, largest1₁₁: int, i₁₂: int ::
              (  2 <= i₁₂
                && i₁₂ < i₃₁
                 ==> largest1₁₁ <= array₂₇[i₁₂]
                    && i₁₂ < 100000
                  ||   largest2₁₀ < array₂₇[i₁₂]
                    && (largest1₁₁ <= array₂₇[i₁₂]
                       ==> false)
                    && i₁₂ < 100000
                  ||   (largest2₁₀ < array₂₇[i₁₂]
                       ==> false)
                    && (largest1₁₁ <= array₂₇[i₁₂]
                       ==> false)
                    && i₁₂ < 100000))
        && 0 <= x₃₂
        && (forall x₂₁: int ::
              (  0 <= x₂₁
                && x₂₁ < x₃₂
                 ==> x₂₁ < 100000))
        && 0 <= x₃₃
        && (forall x₂₄: int ::
              (  0 <= x₂₄
                && x₂₄ < x₃₃
                 ==> x₂₄ < 100000))
        && x₃₃ < 100000
         ==> x₃₂ < 100000
          || i₃₁ < 100000
          || i₂₈ < 100000
          || array₂₇[x₃₃] <= largest2₂₉
          || array₂₇[x₃₃] == largest1₃₀));

goal {:named "assert"} (forall array: [int]int, array₂₇: [int]int, i₂₈: int, largest1₄₆: int, i₄₇: int, x₄₈: int ::
      (  0 <= i₂₈
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₈
                 ==> (exists nondet_int₁₆: int ::
                        i₇ < 100000
                        && array₂₇[i₇] == nondet_int₁₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₈
                || array₂₇[i₇] == array[i₇])
        && 2 <= i₄₇
        && (forall largest2₁₀: int, largest1₁₁: int, i₁₂: int ::
              (  2 <= i₁₂
                && i₁₂ < i₄₇
                 ==> largest1₁₁ <= array₂₇[i₁₂]
                    && i₁₂ < 100000
                  ||   largest2₁₀ < array₂₇[i₁₂]
                    && (largest1₁₁ <= array₂₇[i₁₂]
                       ==> false)
                    && i₁₂ < 100000
                  ||   (largest2₁₀ < array₂₇[i₁₂]
                       ==> false)
                    && (largest1₁₁ <= array₂₇[i₁₂]
                       ==> false)
                    && i₁₂ < 100000))
        && 0 <= x₄₈
        && (forall x₂₁: int ::
              (  0 <= x₂₁
                && x₂₁ < x₄₈
                 ==> x₂₁ < 100000))
        && x₄₈ < 100000
         ==> i₄₇ < 100000
          || array₂₇[0] < array₂₇[1]
          || i₂₈ < 100000
          || array₂₇[x₄₈] <= largest1₄₆));

goal {:named "assert"} (forall array: [int]int, array₂₇: [int]int, i₂₈: int, largest2₄₅: int, largest1₄₆: int, i₄₇: int, x₄₈: int, x₄₉: int ::
      (  0 <= i₂₈
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₈
                 ==> (exists nondet_int₁₆: int ::
                        i₇ < 100000
                        && array₂₇[i₇] == nondet_int₁₆)))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₈
                || array₂₇[i₇] == array[i₇])
        && 2 <= i₄₇
        && (forall largest2₁₀: int, largest1₁₁: int, i₁₂: int ::
              (  2 <= i₁₂
                && i₁₂ < i₄₇
                 ==> largest1₁₁ <= array₂₇[i₁₂]
                    && i₁₂ < 100000
                  ||   largest2₁₀ < array₂₇[i₁₂]
                    && (largest1₁₁ <= array₂₇[i₁₂]
                       ==> false)
                    && i₁₂ < 100000
                  ||   (largest2₁₀ < array₂₇[i₁₂]
                       ==> false)
                    && (largest1₁₁ <= array₂₇[i₁₂]
                       ==> false)
                    && i₁₂ < 100000))
        && 0 <= x₄₈
        && (forall x₂₁: int ::
              (  0 <= x₂₁
                && x₂₁ < x₄₈
                 ==> x₂₁ < 100000))
        && 0 <= x₄₉
        && (forall x₂₄: int ::
              (  0 <= x₂₄
                && x₂₄ < x₄₉
                 ==> x₂₄ < 100000))
        && x₄₉ < 100000
         ==> x₄₈ < 100000
          || i₄₇ < 100000
          || array₂₇[0] < array₂₇[1]
          || i₂₈ < 100000
          || array₂₇[x₄₉] <= largest2₄₅
          || array₂₇[x₄₉] == largest1₄₆));

