data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall x: [int]int, x₂₉: [int]int, i₃₀: int, ret₃₅: int, i₃₆: int, ret₄₁: int, i₄₂: int, x₄₄: [int]int, i₄₅: int, i₅₁: int ::
      (  0 <= i₃₀
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₀
                 ==> (exists nondet_int₃₁₃: int ::
                        -2147483648 <= nondet_int₃₁₃
                        && nondet_int₃₁₃ < 2147483648
                        && i₁₄ < 5
                        && x₂₉[i₁₄] == nondet_int₃₁₃)))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₃₀
                || x₂₉[i₁₄] == x[i₁₄])
        && 0 <= i₃₆
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₆
                 ==> ret₄ < x₂₉[i₅]
                    && i₅ < 5
                  ||   (ret₄ < x₂₉[i₅]
                       ==> false)
                    && i₅ < 5))
        && 0 <= i₄₂
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₂
                 ==> ret₄ < x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₅]
                    && i₅ < 5
                  ||   (ret₄ < x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₅]
                       ==> false)
                    && i₅ < 5))
        && 0 <= i₄₅
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₄₅
                 ==> i₁₉ < 4
                  && x₄₄[i₁₉] == x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][1 + i₁₉]))
        && (forall i₁₉: int ::
                  0 <= i₁₉
                  && i₁₉ < i₄₅
                || x₄₄[i₁₉] == x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₁₉])
        && 0 <= i₅₁
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₁
                 ==> ret₄ < x₄₄[5 - 1 := x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][0]][i₅]
                    && i₅ < 5
                  ||   (ret₄ < x₄₄[5 - 1 := x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][0]][i₅]
                       ==> false)
                    && i₅ < 5))
         ==> ret₃₅ == ret₄₁
          || i₅₁ < 5
          || i₄₅ < 5 - 1
          || i₄₂ < 5
          || i₃₆ < 5
          || i₃₀ < 5));

goal {:named "assert"} (forall x: [int]int, x₂₉: [int]int, i₃₀: int, ret₃₅: int, i₃₆: int, i₄₂: int, x₄₄: [int]int, i₄₅: int, ret₅₀: int, i₅₁: int ::
      (  0 <= i₃₀
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₀
                 ==> (exists nondet_int₃₁₃: int ::
                        -2147483648 <= nondet_int₃₁₃
                        && nondet_int₃₁₃ < 2147483648
                        && i₁₄ < 5
                        && x₂₉[i₁₄] == nondet_int₃₁₃)))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₃₀
                || x₂₉[i₁₄] == x[i₁₄])
        && 0 <= i₃₆
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₆
                 ==> ret₄ < x₂₉[i₅]
                    && i₅ < 5
                  ||   (ret₄ < x₂₉[i₅]
                       ==> false)
                    && i₅ < 5))
        && 0 <= i₄₂
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₂
                 ==> ret₄ < x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₅]
                    && i₅ < 5
                  ||   (ret₄ < x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₅]
                       ==> false)
                    && i₅ < 5))
        && 0 <= i₄₅
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₄₅
                 ==> i₁₉ < 4
                  && x₄₄[i₁₉] == x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][1 + i₁₉]))
        && (forall i₁₉: int ::
                  0 <= i₁₉
                  && i₁₉ < i₄₅
                || x₄₄[i₁₉] == x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₁₉])
        && 0 <= i₅₁
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₁
                 ==> ret₄ < x₄₄[5 - 1 := x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][0]][i₅]
                    && i₅ < 5
                  ||   (ret₄ < x₄₄[5 - 1 := x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][0]][i₅]
                       ==> false)
                    && i₅ < 5))
         ==> ret₃₅ == ret₅₀
          || i₅₁ < 5
          || i₄₅ < 5 - 1
          || i₄₂ < 5
          || i₃₆ < 5
          || i₃₀ < 5));

