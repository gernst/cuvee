data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, f₁₈: int, i₁₉: int ::
      (  0 <= i₁₅
        && i₁₅ <= 100000
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₅
                 ==> (exists __VERIFIER_nondet_int₁₃: int ::
                        i₄ < 100000
                        && a₁₄[i₄] == __VERIFIER_nondet_int₁₃)))
        && (forall i₄: int ::
                  0 <= i₄
                  && i₄ < i₁₅
                || a₁₄[i₄] == a[i₄])
        && 0 <= i₁₇
        && i₁₇ <= 100000
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₁₇
                 ==> 0 <= a₁₄[i₇]
                    && i₇ < 100000
                    && b₁₆[i₇] == 1
                  ||   (0 <= a₁₄[i₇]
                       ==> false)
                    && i₇ < 100000
                    && b₁₆[i₇] == 0))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₁₇
                || b₁₆[i₇] == b[i₇])
        && 0 <= i₁₉
        && i₁₉ <= 100000
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₁₉
                 ==> a₁₄[i₁₁] < 0
                    && (b₁₆[i₁₁] == 0
                       ==> false)
                    && 0 <= a₁₄[i₁₁]
                    && b₁₆[i₁₁] == 0
                    && i₁₁ < 100000
                  ||   a₁₄[i₁₁] < 0
                    && (b₁₆[i₁₁] == 0
                       ==> false)
                    && (  0 <= a₁₄[i₁₁]
                      && b₁₆[i₁₁] == 0
                       ==> false)
                    && i₁₁ < 100000
                  ||   (a₁₄[i₁₁] < 0
                       ==> b₁₆[i₁₁] == 0)
                    && 0 <= a₁₄[i₁₁]
                    && b₁₆[i₁₁] == 0
                    && i₁₁ < 100000
                  ||   (a₁₄[i₁₁] < 0
                       ==> b₁₆[i₁₁] == 0)
                    && (  0 <= a₁₄[i₁₁]
                      && b₁₆[i₁₁] == 0
                       ==> false)
                    && i₁₁ < 100000))
        && f₁₈ == 0
         ==> i₁₉ < 100000
          || i₁₇ < 100000
          || i₁₅ < 100000));

