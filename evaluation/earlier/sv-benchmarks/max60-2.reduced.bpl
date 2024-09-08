data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, x₂₉: [int]int, i₃₀: int, ret₃₅: int, i₃₆: int, ret₄₁: int, i₄₂: int, x₄₄: [int]int, i₄₅: int, i₅₁: int ::
      (  0 <= i₃₀
        && i₃₀ <= 60
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₀
                 ==> (exists __VERIFIER_nondet_int₃₁₃: int ::
                        i₁₄ < 60
                        && x₂₉[i₁₄] == __VERIFIER_nondet_int₃₁₃)))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₃₀
                || x₂₉[i₁₄] == x[i₁₄])
        && 0 <= i₃₆
        && i₃₆ <= 60
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₆
                 ==> ret₄ < x₂₉[i₅]
                    && i₅ < 60
                  ||   (ret₄ < x₂₉[i₅]
                       ==> false)
                    && i₅ < 60))
        && 0 <= i₄₂
        && i₄₂ <= 60
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₂
                 ==> ret₄ < x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₅]
                    && i₅ < 60
                  ||   (ret₄ < x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₅]
                       ==> false)
                    && i₅ < 60))
        && 0 <= i₄₅
        && i₄₅ <= 59
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₄₅
                 ==> i₁₉ < 59
                  && x₄₄[i₁₉] == x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][1 + i₁₉]))
        && (forall i₁₉: int ::
                  0 <= i₁₉
                  && i₁₉ < i₄₅
                || x₄₄[i₁₉] == x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₁₉])
        && 0 <= i₅₁
        && i₅₁ <= 60
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₁
                 ==> ret₄ < x₄₄[60 - 1 := x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][0]][i₅]
                    && i₅ < 60
                  ||   (ret₄ < x₄₄[60 - 1 := x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][0]][i₅]
                       ==> false)
                    && i₅ < 60))
         ==> ret₃₅ == ret₄₁
          || i₅₁ < 60
          || i₄₅ < 60 - 1
          || i₄₂ < 60
          || i₃₆ < 60
          || i₃₀ < 60));

goal (forall x: [int]int, x₂₉: [int]int, i₃₀: int, ret₃₅: int, i₃₆: int, i₄₂: int, x₄₄: [int]int, i₄₅: int, ret₅₀: int, i₅₁: int ::
      (  0 <= i₃₀
        && i₃₀ <= 60
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₀
                 ==> (exists __VERIFIER_nondet_int₃₁₃: int ::
                        i₁₄ < 60
                        && x₂₉[i₁₄] == __VERIFIER_nondet_int₃₁₃)))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₃₀
                || x₂₉[i₁₄] == x[i₁₄])
        && 0 <= i₃₆
        && i₃₆ <= 60
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₆
                 ==> ret₄ < x₂₉[i₅]
                    && i₅ < 60
                  ||   (ret₄ < x₂₉[i₅]
                       ==> false)
                    && i₅ < 60))
        && 0 <= i₄₂
        && i₄₂ <= 60
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₂
                 ==> ret₄ < x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₅]
                    && i₅ < 60
                  ||   (ret₄ < x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₅]
                       ==> false)
                    && i₅ < 60))
        && 0 <= i₄₅
        && i₄₅ <= 59
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₄₅
                 ==> i₁₉ < 59
                  && x₄₄[i₁₉] == x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][1 + i₁₉]))
        && (forall i₁₉: int ::
                  0 <= i₁₉
                  && i₁₉ < i₄₅
                || x₄₄[i₁₉] == x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][i₁₉])
        && 0 <= i₅₁
        && i₅₁ <= 60
        && (forall ret₄: int, i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₁
                 ==> ret₄ < x₄₄[60 - 1 := x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][0]][i₅]
                    && i₅ < 60
                  ||   (ret₄ < x₄₄[60 - 1 := x₂₉[0 := x₂₉[1]][1 := x₂₉[0]][0]][i₅]
                       ==> false)
                    && i₅ < 60))
         ==> ret₃₅ == ret₅₀
          || i₅₁ < 60
          || i₄₅ < 60 - 1
          || i₄₂ < 60
          || i₃₆ < 60
          || i₃₀ < 60));

