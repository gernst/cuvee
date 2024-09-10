data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall a: [int]int, a₁₃: [int]int, i₁₄: int, min₁₅: int, i₁₆: int, x₁₇: int ::
      (  0 <= i₁₄
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₄
                 ==> (exists nondet_int₁₂: int ::
                        -2147483648 <= nondet_int₁₂
                        && nondet_int₁₂ < 2147483648
                        && i₃ < 100000
                        && a₁₃[i₃] == nondet_int₁₂)))
        && (forall i₃: int ::
                  0 <= i₃
                  && i₃ < i₁₄
                || a₁₃[i₃] == a[i₃])
        && 0 <= i₁₆
        && (forall min₆: int, i₇: int ::
              (  0 <= i₇
                && i₇ < i₁₆
                 ==> a₁₃[i₇] < min₆
                    && i₇ < 100000
                  ||   (a₁₃[i₇] < min₆
                       ==> false)
                    && i₇ < 100000))
        && 0 <= x₁₇
        && (forall x₁₁: int ::
              (  0 <= x₁₁
                && x₁₁ < x₁₇
                 ==> x₁₁ < 100000))
        && x₁₇ < 100000
         ==> i₁₆ < 100000
          || i₁₄ < 100000
          || min₁₅ <= a₁₃[x₁₇]));

