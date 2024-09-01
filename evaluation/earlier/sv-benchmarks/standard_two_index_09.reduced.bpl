data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, b₁₈: [int]int, i₁₉: int, a₂₀: [int]int, i₂₁: int, j₂₂: int ::
      (  0 <= i₁₉
        && i₁₉ <= 100000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉
                        && b₁₈[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉)
                || b₁₈[x₅] == b[x₅])
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> i₄ < 100000))
        && 0 <= j₂₂
        && i₂₁ <= 100000
        && (forall x₁₀: int, j₉: int ::
              (  x₁₀ == j₉
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> (exists i₈: int, j₉: int ::
                        i₈ < 100000
                        && x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂
                        && a₂₀[x₁₀] == b₁₈[i₈])))
        && (forall x₁₀: int ::
                (exists j₉: int ::
                        x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂)
                || a₂₀[x₁₀] == a[x₁₀])
        && (forall i₈: int, j₉: int ::
              (  j₉ <= j₉
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> i₈ < 100000))
        && i₂₁ < 100000
         ==> i₁₉ < 100000
          || i₂₁ + 9 <= 100000));

goal (forall a: [int]int, b: [int]int, b₁₈: [int]int, i₁₉: int, a₂₀: [int]int, i₂₁: int, j₂₂: int, i₈: int, j₉: int ::
      (  0 <= i₁₉
        && i₁₉ <= 100000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉
                        && b₁₈[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉)
                || b₁₈[x₅] == b[x₅])
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> i₄ < 100000))
        && 0 <= j₂₂
        && i₂₁ <= 100000
        && (forall x₁₀: int, j₁₂₁: int ::
              (  x₁₀ == j₁₂₁
                && 0 <= j₁₂₁
                && j₁₂₁ < j₂₂
                 ==> (exists i₁₂₃: int, j₁₂₂: int ::
                        i₁₂₃ < 100000
                        && x₁₀ == j₁₂₂
                        && 0 <= j₁₂₂
                        && j₁₂₂ < j₂₂
                        && a₂₀[x₁₀] == b₁₈[i₁₂₃])))
        && (forall x₁₀: int ::
                (exists j₁₂₄: int ::
                        x₁₀ == j₁₂₄
                        && 0 <= j₁₂₄
                        && j₁₂₄ < j₂₂)
                || a₂₀[x₁₀] == a[x₁₀])
        && (forall i₁₂₆: int, j₁₂₅: int ::
              (  j₁₂₅ <= j₁₂₅
                && 0 <= j₁₂₅
                && j₁₂₅ < j₂₂
                 ==> i₁₂₆ < 100000))
        && i₂₁ < 100000
        && j₉ <= j₉
        && 0 <= j₉
        && j₉ < j₂₂ + 1
         ==> i₁₉ < 100000
          || i₈ < 100000));

goal (forall a: [int]int, b: [int]int, b₁₈: [int]int, i₁₉: int, a₂₀: [int]int, i₂₁: int, j₂₂: int, i₂₃: int, j₂₄: int ::
      (  0 <= i₁₉
        && i₁₉ <= 100000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉
                        && b₁₈[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉)
                || b₁₈[x₅] == b[x₅])
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> i₄ < 100000))
        && 0 <= j₂₂
        && i₂₁ <= 100000
        && (forall x₁₀: int, j₉: int ::
              (  x₁₀ == j₉
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> (exists i₈: int, j₉: int ::
                        i₈ < 100000
                        && x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂
                        && a₂₀[x₁₀] == b₁₈[i₈])))
        && (forall x₁₀: int ::
                (exists j₉: int ::
                        x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂)
                || a₂₀[x₁₀] == a[x₁₀])
        && (forall i₈: int, j₉: int ::
              (  j₉ <= j₉
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> i₈ < 100000))
        && 0 <= j₂₄
        && i₂₃ <= 100000
        && (forall i₁₄: int, j₁₅: int ::
              (  j₁₅ <= j₁₅
                && 0 <= j₁₅
                && j₁₅ < j₂₄
                 ==> i₁₄ < 100000))
        && i₂₃ < 100000
         ==> i₂₁ < 100000
          || i₁₉ < 100000
          || a₂₀[j₂₄] == b₁₈[9 * j₂₄ + 1]));

goal (forall a: [int]int, b: [int]int, b₁₈: [int]int, i₁₉: int, a₂₀: [int]int, i₂₁: int, j₂₂: int, i₂₃: int, j₂₄: int ::
      (  0 <= i₁₉
        && i₁₉ <= 100000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉
                        && b₁₈[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉)
                || b₁₈[x₅] == b[x₅])
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> i₄ < 100000))
        && 0 <= j₂₂
        && i₂₁ <= 100000
        && (forall x₁₀: int, j₉: int ::
              (  x₁₀ == j₉
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> (exists i₈: int, j₉: int ::
                        i₈ < 100000
                        && x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂
                        && a₂₀[x₁₀] == b₁₈[i₈])))
        && (forall x₁₀: int ::
                (exists j₉: int ::
                        x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂)
                || a₂₀[x₁₀] == a[x₁₀])
        && (forall i₈: int, j₉: int ::
              (  j₉ <= j₉
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> i₈ < 100000))
        && 0 <= j₂₄
        && i₂₃ <= 100000
        && (forall i₁₄: int, j₁₅: int ::
              (  j₁₅ <= j₁₅
                && 0 <= j₁₅
                && j₁₅ < j₂₄
                 ==> i₁₄ < 100000))
        && i₂₃ < 100000
         ==> i₂₁ < 100000
          || i₁₉ < 100000
          || i₂₃ + 9 <= 100000));

goal (forall a: [int]int, b: [int]int, b₁₈: [int]int, i₁₉: int, a₂₀: [int]int, i₂₁: int, j₂₂: int, i₂₃: int, j₂₄: int, i₁₄: int, j₁₅: int ::
      (  0 <= i₁₉
        && i₁₉ <= 100000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉
                        && b₁₈[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₉)
                || b₁₈[x₅] == b[x₅])
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < i₁₉
                 ==> i₄ < 100000))
        && 0 <= j₂₂
        && i₂₁ <= 100000
        && (forall x₁₀: int, j₉: int ::
              (  x₁₀ == j₉
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> (exists i₈: int, j₉: int ::
                        i₈ < 100000
                        && x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂
                        && a₂₀[x₁₀] == b₁₈[i₈])))
        && (forall x₁₀: int ::
                (exists j₉: int ::
                        x₁₀ == j₉
                        && 0 <= j₉
                        && j₉ < j₂₂)
                || a₂₀[x₁₀] == a[x₁₀])
        && (forall i₈: int, j₉: int ::
              (  j₉ <= j₉
                && 0 <= j₉
                && j₉ < j₂₂
                 ==> i₈ < 100000))
        && 0 <= j₂₄
        && i₂₃ <= 100000
        && (forall i₁₈₈: int, j₁₈₉: int ::
              (  j₁₈₉ <= j₁₈₉
                && 0 <= j₁₈₉
                && j₁₈₉ < j₂₄
                 ==> i₁₈₈ < 100000))
        && i₂₃ < 100000
        && j₁₅ <= j₁₅
        && 0 <= j₁₅
        && j₁₅ < j₂₄ + 1
         ==> i₂₁ < 100000
          || i₁₉ < 100000
          || i₁₄ < 100000));

