data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var SIZE: int;

var MAX: int;

procedure main()
  returns (c#result: int)
  modifies SIZE, MAX;
{
  SIZE := 0;
  MAX := 100000;
  havoc SIZE;
  assume -2147483648 <= SIZE && SIZE < 2147483648;
  if(1 < SIZE && SIZE < MAX) {
    var i: int;
    var a: [int]int;
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₅: int ::
              (  old(i) <= i₅
                && i₅ < i
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < SIZE
                        && a[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
              (!(  old(i) <= i₅
                && i₅ < i
              )
                 ==> a[i₅] == old(a)[i₅]));
    {
      var nondet_int₁: int;
      assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
      a[i] := nondet_int₁;
      i := i + 1;
    }
    if(SIZE % 2 != 0) {
      c#result := 1;
      return;
    }
    assume SIZE % 2 == 0;
    i := 1;
    while(i <= SIZE / 2)
      decreases SIZE / 2 + 1 - i;
      invariant old(i) <= i
        && (forall i₈: int ::
              (  old(i) <= i₈
                && i₈ < i
                 ==> -1 + 2 * i₈ < a[-2 + 2 * i₈ := -2 + 2 * i₈][-1 + 2 * i₈]
                    && -2 + 2 * i₈ < a[-2 + 2 * i₈]
                    && i₈ <= SIZE / 2
                    && a[-1 + 2 * i₈] == -1 + 2 * i₈
                    && (-2 + 2 * i₈ != -1 + 2 * i₈
                       ==> a[-2 + 2 * i₈] == -2 + 2 * i₈)
                  ||   -1 + 2 * i₈ < a[-1 + 2 * i₈]
                    && !(-2 + 2 * i₈ < a[-2 + 2 * i₈]
                    )
                    && i₈ <= SIZE / 2
                    && a[-1 + 2 * i₈] == -1 + 2 * i₈
                  ||   !(-1 + 2 * i₈ < a[-2 + 2 * i₈ := -2 + 2 * i₈][-1 + 2 * i₈]
                    )
                    && -2 + 2 * i₈ < a[-2 + 2 * i₈]
                    && i₈ <= SIZE / 2
                    && a[-2 + 2 * i₈] == -2 + 2 * i₈
                  ||   !(-1 + 2 * i₈ < a[-1 + 2 * i₈]
                    )
                    && !(-2 + 2 * i₈ < a[-2 + 2 * i₈]
                    )
                    && i₈ <= SIZE / 2))
        && (forall i₈: int ::
              (!(  old(i) <= i₈
                && i₈ < i
              )
                 ==> a[-1 + 2 * i₈] == old(a)[-1 + 2 * i₈]
                  && a[-2 + 2 * i₈] == old(a)[-2 + 2 * i₈]));
    {
      if(2 * i - 2 < a[2 * i - 2]) {
        a[((2 * i) - 2)] := 2 * i - 2;
      }
      if(2 * i - 1 < a[2 * i - 1]) {
        a[((2 * i) - 1)] := 2 * i - 1;
      }
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₁₁: int ::
              (  old(i) <= i₁₁
                && i₁₁ < i
                 ==> i₁₁ < SIZE));
    {
      assert a[i] <= i;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

