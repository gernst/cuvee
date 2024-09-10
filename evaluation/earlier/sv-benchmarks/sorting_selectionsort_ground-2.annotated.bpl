data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var i: int := 0;
  var x: int;
  var y: int;
  {
    var i: int := 0;
    while(i < 100000)
      decreases 100000 - i;
      invariant old(i) <= i
        && (forall i₅: int ::
              (  old(i) <= i₅
                && i₅ < i
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
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
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂₄: int ::
            (  old(i) <= i₂₄
              && i₂₄ < i
               ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                        i₂₄ <= x₂₁
                        && (forall x₂₀: int ::
                              (  i₂₄ <= x₂₀
                                && x₂₀ < x₂₁
                                 ==> x₂₀ < 100000))
                        && !(x₂₁ < 100000
                        )
                        && 0 <= x₁₇
                        && (forall x₁₅: int ::
                              (  0 <= x₁₅
                                && x₁₅ < x₁₇
                                 ==> (exists y₁₃: int ::
                                        1 + x₁₅ <= y₁₃
                                        && (forall y₁₂: int ::
                                              (  1 + x₁₅ <= y₁₂
                                                && y₁₂ < y₁₃
                                                 ==> y₁₂ < i₂₄))
                                        && !(y₁₃ < i₂₄
                                        )
                                        && x₁₅ < i₂₄)))
                        && !(x₁₇ < i₂₄
                        )
                        && s₁₀ != i₂₄
                        && 1 + i₂₄ <= k₁₁
                        && (forall s₈: int, k₉: int ::
                              (  1 + i₂₄ <= k₉
                                && k₉ < k₁₁
                                 ==> a[k₉] < a[s₈]
                                    && k₉ < 100000
                                  ||   !(a[k₉] < a[s₈]
                                    )
                                    && k₉ < 100000))
                        && !(k₁₁ < 100000
                        )
                        && i₂₄ < 100000
                        && a[i₂₄] == old(a)[s₁₀]
                        && (s₁₀ != i₂₄
                           ==> a[s₁₀] == old(a)[i₂₄]))
                || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                        i₂₄ <= x₂₂
                        && (forall x₂₀: int ::
                              (  i₂₄ <= x₂₀
                                && x₂₀ < x₂₂
                                 ==> x₂₀ < 100000))
                        && !(x₂₂ < 100000
                        )
                        && 0 <= x₁₉
                        && (forall x₁₅: int ::
                              (  0 <= x₁₅
                                && x₁₅ < x₁₉
                                 ==> (exists y₁₃: int ::
                                        1 + x₁₅ <= y₁₃
                                        && (forall y₁₂: int ::
                                              (  1 + x₁₅ <= y₁₂
                                                && y₁₂ < y₁₃
                                                 ==> y₁₂ < i₂₄))
                                        && !(y₁₃ < i₂₄
                                        )
                                        && x₁₅ < i₂₄)))
                        && !(x₁₉ < i₂₄
                        )
                        && s₁₀ == i₂₄
                        && 1 + i₂₄ <= k₁₁
                        && (forall s₈: int, k₉: int ::
                              (  1 + i₂₄ <= k₉
                                && k₉ < k₁₁
                                 ==> a[k₉] < a[s₈]
                                    && k₉ < 100000
                                  ||   !(a[k₉] < a[s₈]
                                    )
                                    && k₉ < 100000))
                        && !(k₁₁ < 100000
                        )
                        && i₂₄ < 100000)))
      && (forall i₂₄: int ::
            (!(  old(i) <= i₂₄
              && i₂₄ < i
            )
               ==> (forall s₁₀: int ::
                      a[i₂₄] == old(a)[i₂₄]
                      && a[s₁₀] == old(a)[s₁₀])));
  {
    var k: int := i + 1;
    var s: int := i;
    while(k < 100000)
      decreases 100000 - k;
      invariant old(k) <= k
        && (forall s₈: int, k₉: int ::
              (  old(k) <= k₉
                && k₉ < k
                 ==> a[k₉] < a[s₈]
                    && k₉ < 100000
                  ||   !(a[k₉] < a[s₈]
                    )
                    && k₉ < 100000));
    {
      if(a[k] < a[s]) {
        s := k;
      }
      k := k + 1;
    }
    if(s != i) {
      var tmp: int := a[s];
      a[s] := a[i];
      a[i] := tmp;
    }
    x := 0;
    while(x < i)
      decreases i - x;
      invariant old(x) <= x
        && (forall x₁₅: int ::
              (  old(x) <= x₁₅
                && x₁₅ < x
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i))
                        && !(y₁₃ < i
                        )
                        && x₁₅ < i)));
    {
      y := x + 1;
      while(y < i)
        decreases i - y;
        invariant old(y) <= y
          && (forall y₁₂: int ::
                (  old(y) <= y₁₂
                  && y₁₂ < y
                   ==> y₁₂ < i));
      {
        assert a[x] <= a[y];
        y := y + 1;
      }
      x := x + 1;
    }
    x := i;
    while(x < 100000)
      decreases 100000 - x;
      invariant old(x) <= x
        && (forall x₂₀: int ::
              (  old(x) <= x₂₀
                && x₂₀ < x
                 ==> x₂₀ < 100000));
    {
      assert a[i] <= a[x];
      x := x + 1;
    }
    i := i + 1;
  }
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₃₃: int ::
            (  old(x) <= x₃₃
              && x₃₃ < x
               ==> (exists y₃₁: int ::
                      1 + x₃₃ <= y₃₁
                      && (forall y₃₀: int ::
                            (  1 + x₃₃ <= y₃₀
                              && y₃₀ < y₃₁
                               ==> y₃₀ < 100000))
                      && !(y₃₁ < 100000
                      )
                      && x₃₃ < 100000)));
  {
    y := x + 1;
    while(y < 100000)
      decreases 100000 - y;
      invariant old(y) <= y
        && (forall y₃₀: int ::
              (  old(y) <= y₃₀
                && y₃₀ < y
                 ==> y₃₀ < 100000));
    {
      assert a[x] <= a[y];
      y := y + 1;
    }
    x := x + 1;
  }
  c#result := 0;
  return;
}

