data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall S: int, a: [int]int, acopy: [int]int, acopy₁₀: [int]int, i₁₁: int, i₅: int ::
      (  -2147483648 <= S
        && S < 2147483648
        && 1 < S
        && S < 1073741823
        && 0 <= i₁₁
        && (forall i₈₀: int ::
              (  0 <= i₈₀
                && i₈₀ < i₁₁
                 ==> i₈₀ < S
                  && acopy₁₀[i₈₀] == a[i₈₀]
                  &&   -1 + -i₈₀ + 2 * S == i₈₀
                    || acopy₁₀[-1 + -i₈₀ + 2 * S] == a[1 + -i₈₀ + 2 * S]))
        && (forall i₈₁: int ::
                  0 <= i₈₁
                  && i₈₁ < i₁₁
                ||   acopy₁₀[i₈₁] == acopy[i₈₁]
                  && acopy₁₀[-1 + -i₈₁ + 2 * S] == acopy[-1 + -i₈₁ + 2 * S])
        && i₁₁ < S
         ==> i₅ < i₁₁ + 1
          || acopy₁₀[2 * S - i₁₁ + 1 := a[2 * S - i₁₁ + 1]][i₁₁ := a[i₁₁]][i₅] == acopy[i₅]));

goal {:named "invariant forward"} (forall S: int, a: [int]int, acopy: [int]int, acopy₁₀: [int]int, i₁₁: int, i₅: int ::
      (  -2147483648 <= S
        && S < 2147483648
        && 1 < S
        && S < 1073741823
        && 0 <= i₁₁
        && (forall i₈₈: int ::
              (  0 <= i₈₈
                && i₈₈ < i₁₁
                 ==> i₈₈ < S
                  && acopy₁₀[i₈₈] == a[i₈₈]
                  &&   -1 + -i₈₈ + 2 * S == i₈₈
                    || acopy₁₀[-1 + -i₈₈ + 2 * S] == a[1 + -i₈₈ + 2 * S]))
        && (forall i₈₉: int ::
                  0 <= i₈₉
                  && i₈₉ < i₁₁
                ||   acopy₁₀[i₈₉] == acopy[i₈₉]
                  && acopy₁₀[-1 + -i₈₉ + 2 * S] == acopy[-1 + -i₈₉ + 2 * S])
        && i₁₁ < S
         ==> i₅ < i₁₁ + 1
          || acopy₁₀[2 * S - i₁₁ + 1 := a[2 * S - i₁₁ + 1]][i₁₁ := a[i₁₁]][-1 + -i₅ + 2 * S] == acopy[-1 + -i₅ + 2 * S]));

goal {:named "assert"} (forall S: int, a: [int]int, acopy: [int]int, acopy₁₀: [int]int, i₁₁: int, i₁₂: int ::
      (  -2147483648 <= S
        && S < 2147483648
        && 1 < S
        && S < 1073741823
        && 0 <= i₁₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₁
                 ==> i₅ < S
                  && acopy₁₀[i₅] == a[i₅]
                  &&   -1 + -i₅ + 2 * S == i₅
                    || acopy₁₀[-1 + -i₅ + 2 * S] == a[1 + -i₅ + 2 * S]))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₁
                ||   acopy₁₀[i₅] == acopy[i₅]
                  && acopy₁₀[-1 + -i₅ + 2 * S] == acopy[-1 + -i₅ + 2 * S])
        && 0 <= i₁₂
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₂
                 ==> i₈ < 2 * S))
        && i₁₂ < 2 * S
         ==> i₁₁ < S
          || acopy₁₀[i₁₂] == a[i₁₂]));

