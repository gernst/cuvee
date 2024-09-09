data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall CELLCOUNT₁₀: int, MINVAL: int, volArray: [int]int, volArray₁₁: [int]int, i₁₂: int, i₁₃: int ::
      (  1 < CELLCOUNT₁₀
        && CELLCOUNT₁₀ % 4 == 0
        && CELLCOUNT₁₀ % 4 == 0
        && 1 <= i₁₂
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₂
                 ==> MINVAL <= 1
                    && MINVAL <= 3
                    && MINVAL <= 7
                    && MINVAL <= 5
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 1
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 3
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 7
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 5
                  ||   MINVAL <= 1
                    && MINVAL <= 3
                    && MINVAL <= 7
                    && (MINVAL <= 5
                       ==> false)
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 1
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 3
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 7
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 0
                  ||   MINVAL <= 1
                    && MINVAL <= 3
                    && (MINVAL <= 7
                       ==> false)
                    && MINVAL <= 5
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 1
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 3
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 0
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 5
                  ||   MINVAL <= 1
                    && MINVAL <= 3
                    && (MINVAL <= 7
                       ==> false)
                    && (MINVAL <= 5
                       ==> false)
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 1
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 3
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 0
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 0
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)
                    && MINVAL <= 7
                    && MINVAL <= 5
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 1
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 0
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 7
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 5
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)
                    && MINVAL <= 7
                    && (MINVAL <= 5
                       ==> false)
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 1
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 0
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 7
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 0
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)
                    && (MINVAL <= 7
                       ==> false)
                    && MINVAL <= 5
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 1
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 0
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 0
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 5
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)
                    && (MINVAL <= 7
                       ==> false)
                    && (MINVAL <= 5
                       ==> false)
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 1
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 0
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 0
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 0
                  ||   (MINVAL <= 1
                       ==> false)
                    && MINVAL <= 3
                    && MINVAL <= 7
                    && MINVAL <= 5
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 0
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 3
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 7
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 5
                  ||   (MINVAL <= 1
                       ==> false)
                    && MINVAL <= 3
                    && MINVAL <= 7
                    && (MINVAL <= 5
                       ==> false)
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 0
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 3
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 7
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 0
                  ||   (MINVAL <= 1
                       ==> false)
                    && MINVAL <= 3
                    && (MINVAL <= 7
                       ==> false)
                    && MINVAL <= 5
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 0
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 3
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 0
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 5
                  ||   (MINVAL <= 1
                       ==> false)
                    && MINVAL <= 3
                    && (MINVAL <= 7
                       ==> false)
                    && (MINVAL <= 5
                       ==> false)
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 0
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 3
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 0
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 0
                  ||   (MINVAL <= 1
                       ==> false)
                    && (MINVAL <= 3
                       ==> false)
                    && MINVAL <= 7
                    && MINVAL <= 5
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 0
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 0
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 7
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 5
                  ||   (MINVAL <= 1
                       ==> false)
                    && (MINVAL <= 3
                       ==> false)
                    && MINVAL <= 7
                    && (MINVAL <= 5
                       ==> false)
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 0
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 0
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 7
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 0
                  ||   (MINVAL <= 1
                       ==> false)
                    && (MINVAL <= 3
                       ==> false)
                    && (MINVAL <= 7
                       ==> false)
                    && MINVAL <= 5
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 0
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 0
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 0
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 5
                  ||   (MINVAL <= 1
                       ==> false)
                    && (MINVAL <= 3
                       ==> false)
                    && (MINVAL <= 7
                       ==> false)
                    && (MINVAL <= 5
                       ==> false)
                    && i₅ <= CELLCOUNT₁₀ / 4
                    && volArray₁₁[-1 + 4 * i₅] == 0
                    &&   -2 + 4 * i₅ == -1 + 4 * i₅
                      || volArray₁₁[-2 + 4 * i₅] == 0
                    &&   -3 + 4 * i₅ == -1 + 4 * i₅
                      || -3 + 4 * i₅ == -2 + 4 * i₅
                      || volArray₁₁[-3 + 4 * i₅] == 0
                    &&   -4 + 4 * i₅ == -1 + 4 * i₅
                      || -4 + 4 * i₅ == -2 + 4 * i₅
                      || -4 + 4 * i₅ == -3 + 4 * i₅
                      || volArray₁₁[-4 + 4 * i₅] == 0))
        && (forall i₅: int ::
                  1 <= i₅
                  && i₅ < i₁₂
                ||   volArray₁₁[-1 + 4 * i₅] == volArray[-1 + 4 * i₅]
                  && volArray₁₁[-2 + 4 * i₅] == volArray[-2 + 4 * i₅]
                  && volArray₁₁[-3 + 4 * i₅] == volArray[-3 + 4 * i₅]
                  && volArray₁₁[-4 + 4 * i₅] == volArray[-4 + 4 * i₅])
        && 0 <= i₁₃
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₃
                 ==> i₈ < CELLCOUNT₁₀))
        && i₁₃ < CELLCOUNT₁₀
         ==> i₁₂ <= CELLCOUNT₁₀ / 4
          || MINVAL <= volArray₁₁[i₁₃]
          || volArray₁₁[i₁₃] == 0));

