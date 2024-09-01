data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall CELLCOUNT₁₁: int, MINVAL: int, volArray: [int]int, x₆: int, i₅: int ::
      (  1 < CELLCOUNT₁₁
        && CELLCOUNT₁₁ % 4 == 0
        && CELLCOUNT₁₁ % 4 == 0
        && (x₆ == -1 + 4 * i₅
           ==> 1 <= i₅
            && i₅ < 1)
        && (x₆ == -2 + 4 * i₅
           ==> x₆ == -1 + 4 * i₅
            ||   x₆ == -2 + 4 * i₅
              && 1 <= i₅
              && i₅ < 1)
        && MINVAL <= 1
        && MINVAL <= 1
        && MINVAL <= 1
        && MINVAL <= 1
        && MINVAL <= 1
        && MINVAL <= 1
        && MINVAL <= 1
        && MINVAL <= 1
         ==> (exists i₅₅: int ::
                  MINVAL <= 1
                  && MINVAL <= 3
                  && MINVAL <= 7
                  && MINVAL <= 5
                  && i₅₅ <= CELLCOUNT₁₁ / 4
                  && if(x₆ == -1 + 4 * i₅₅) then 1 <= i₅₅ && i₅₅ < 1 && volArray[x₆] == 1 else if(x₆ == -2 + 4 * i₅₅) then 1 <= i₅₅ && i₅₅ < 1 && volArray[x₆] == 3 else if(x₆ == -3 + 4 * i₅₅) then 1 <= i₅₅ && i₅₅ < 1 && volArray[x₆] == 7 else x₆ == -4 + 4 * i₅₅ && 1 <= i₅₅ && i₅₅ < 1 && volArray[x₆] == 5)
          ||   MINVAL <= 1
            && MINVAL <= 3
            && MINVAL <= 7
            && (MINVAL <= 5
               ==> false)
          ||   MINVAL <= 1
            && MINVAL <= 3
            && (MINVAL <= 7
               ==> false)
          ||   MINVAL <= 1
            && MINVAL <= 3
            && (MINVAL <= 7
               ==> false)
          ||   MINVAL <= 1
            && (MINVAL <= 3
               ==> false)
          ||   MINVAL <= 1
            && (MINVAL <= 3
               ==> false)
          ||   MINVAL <= 1
            && (MINVAL <= 3
               ==> false)
          ||   MINVAL <= 1
            && (MINVAL <= 3
               ==> false)));

goal (forall CELLCOUNT₁₁: int, MINVAL: int, volArray: [int]int, volArray₁₂: [int]int, i₁₃: int, i₁₄: int ::
      (  1 < CELLCOUNT₁₁
        && CELLCOUNT₁₁ % 4 == 0
        && CELLCOUNT₁₁ % 4 == 0
        && 1 <= i₁₃
        && i₁₃ <= 1 + CELLCOUNT₁₁ / 4
        && (forall x₆: int, i₅: int ::
              (  (x₆ == -1 + 4 * i₅
                   ==> 1 <= i₅
                    && i₅ < i₁₃)
                && (x₆ == -2 + 4 * i₅
                   ==> x₆ == -1 + 4 * i₅
                    ||   x₆ == -2 + 4 * i₅
                      && 1 <= i₅
                      && i₅ < i₁₃)
                && MINVAL <= 1
                && MINVAL <= 1
                && MINVAL <= 1
                && MINVAL <= 1
                && MINVAL <= 1
                && MINVAL <= 1
                && MINVAL <= 1
                && MINVAL <= 1
                 ==> (exists i₅: int ::
                          MINVAL <= 1
                          && MINVAL <= 3
                          && MINVAL <= 7
                          && MINVAL <= 5
                          && i₅ <= CELLCOUNT₁₁ / 4
                          && if(x₆ == -1 + 4 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 1 else if(x₆ == -2 + 4 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 3 else if(x₆ == -3 + 4 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 7 else x₆ == -4 + 4 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 5)
                  ||   MINVAL <= 1
                    && MINVAL <= 3
                    && MINVAL <= 7
                    && (MINVAL <= 5
                       ==> false)
                  ||   MINVAL <= 1
                    && MINVAL <= 3
                    && (MINVAL <= 7
                       ==> false)
                  ||   MINVAL <= 1
                    && MINVAL <= 3
                    && (MINVAL <= 7
                       ==> false)
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)))
        && (forall x₆: int ::
                (exists i₅: int ::
                      if(x₆ == -1 + 4 * i₅) then 1 <= i₅ && i₅ < i₁₃ else if(x₆ == -2 + 4 * i₅) then 1 <= i₅ && i₅ < i₁₃ else if(x₆ == -3 + 4 * i₅) then 1 <= i₅ && i₅ < i₁₃ else x₆ == -4 + 4 * i₅ && 1 <= i₅ && i₅ < i₁₃)
                || volArray₁₂[x₆] == volArray[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 1 <= i₅
                && i₅ < i₁₃
                 ==> i₅ <= CELLCOUNT₁₁ / 4))
        && 0 <= i₁₄
        && i₁₄ <= CELLCOUNT₁₁
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₁₄
                 ==> i₉ < CELLCOUNT₁₁))
        && i₁₄ < CELLCOUNT₁₁
         ==> i₁₃ <= CELLCOUNT₁₁ / 4
          || MINVAL <= volArray₁₂[i₁₄]
          || volArray₁₂[i₁₄] == 0));

