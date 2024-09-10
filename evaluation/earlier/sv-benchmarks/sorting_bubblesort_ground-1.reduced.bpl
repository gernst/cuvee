data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant entry"} (forall a: [int]int, a₂₂: [int]int, j₂₃: int, swapped₁₁: int ::
      (  0 <= j₂₃
        && (forall j₃: int ::
              (  0 <= j₃
                && j₃ < j₂₃
                 ==> (exists nondet_int₁₂: int ::
                        -2147483648 <= nondet_int₁₂
                        && nondet_int₁₂ < 2147483648
                        && j₃ < 100000
                        && a₂₂[j₃] == nondet_int₁₂)))
        && (forall j₃: int ::
                  0 <= j₃
                  && j₃ < j₂₃
                || a₂₂[j₃] == a[j₃])
         ==> j₂₃ < 100000
          || (exists a₈: [int]int, i₁₀: int ::
                  1 <= i₁₀
                  && (forall i₇: int ::
                        (  1 <= i₇
                          && i₇ < i₁₀
                           ==> a₈[i₇] < a₈[-1 + i₇]
                              && i₇ < 100000
                              && a₈[-1 + i₇] == a₂₂[i₇]
                              &&   i₇ == -1 + i₇
                                || a₈[i₇] == a₂₂[-1 + i₇]
                            ||   (a₈[i₇] < a₈[-1 + i₇]
                                 ==> false)
                              && i₇ < 100000))
                  && (forall i₇: int ::
                            1 <= i₇
                            && i₇ < i₁₀
                          ||   a₈[-1 + i₇] == a₂₂[-1 + i₇]
                            && a₈[i₇] == a₂₂[i₇])
                  && (i₁₀ < 100000
                     ==> false)
                  && (swapped₁₁ == 0
                     ==> false))));

