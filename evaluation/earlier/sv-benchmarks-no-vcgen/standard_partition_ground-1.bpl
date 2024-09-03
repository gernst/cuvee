data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var aa: [int]int;
  var a: int := 0;
  var b: int := 0;
  var c: int := 0;
  var bb: [int]int;
  var cc: [int]int;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && 0 <= b
      && 0 <= a
      && a <= 100000
      && (forall x₇: int ::
            ((exists a₆: int ::
                    x₇ == a₆
                    && 0 <= a₆
                    && a₆ < a)
               ==> (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                        0 <= aa[a₆ := __VERIFIER_nondet_int₁₄][a₆]
                        && a₆ < 100000
                        && x₇ == a₆
                        && 0 <= a₆
                        && a₆ < a
                        && aa[x₇] == __VERIFIER_nondet_int₁₄)
                || (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                        !(0 <= aa[a₆ := __VERIFIER_nondet_int₁₄][a₆]
                        )
                        && a₆ < 100000
                        && x₇ == a₆
                        && 0 <= a₆
                        && a₆ < a
                        && aa[x₇] == __VERIFIER_nondet_int₁₄)))
      && (forall x₇: int ::
            (!((exists a₆: int ::
                    x₇ == a₆
                    && 0 <= a₆
                    && a₆ < a)
            )
               ==> aa[x₇] == old(aa[x₇])))
      && (forall x₈: int ::
            ((exists b₅: int ::
                    x₈ == b₅
                    && 0 <= b₅
                    && b₅ < b)
               ==> (exists __VERIFIER_nondet_int₁₄: int, b₅: int, a₆: int ::
                      0 <= aa[a₆ := __VERIFIER_nondet_int₁₄][a₆]
                      && a₆ < 100000
                      && x₈ == b₅
                      && 0 <= b₅
                      && b₅ < b
                      && bb[x₈] == aa[a₆ := __VERIFIER_nondet_int₁₄][a₆])))
      && (forall x₈: int ::
            (!((exists b₅: int ::
                    x₈ == b₅
                    && 0 <= b₅
                    && b₅ < b)
            )
               ==> bb[x₈] == old(bb[x₈])))
      && (forall b₅: int, a₆: int ::
            (  0 <= b₅
              && 0 <= a₆
              && b₅ < b
              && a₆ < a
               ==> a₆ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    aa := aa[a := __VERIFIER_nondet_int₁];
    if(0 <= aa[a]) {
      bb := bb[b := aa[a]];
      b := b + 1;
    }
    a := a + 1;
  }
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && 0 <= c
      && 0 <= a
      && a <= 100000
      && (forall x₁₅: int ::
            ((exists c₁₃: int ::
                    x₁₅ == c₁₃
                    && 0 <= c₁₃
                    && c₁₃ < c)
               ==> (exists c₁₃: int, a₁₄: int ::
                      0 <= aa[a₁₄]
                      && a₁₄ < 100000
                      && x₁₅ == c₁₃
                      && 0 <= c₁₃
                      && c₁₃ < c
                      && cc[x₁₅] == aa[a₁₄])))
      && (forall x₁₅: int ::
            (!((exists c₁₃: int ::
                    x₁₅ == c₁₃
                    && 0 <= c₁₃
                    && c₁₃ < c)
            )
               ==> cc[x₁₅] == old(cc[x₁₅])))
      && (forall c₁₃: int, a₁₄: int ::
            (  0 <= c₁₃
              && 0 <= a₁₄
              && c₁₃ < c
              && a₁₄ < a
               ==> a₁₄ < 100000));
  {
    if(0 <= aa[a]) {
      cc := cc[c := aa[a]];
      c := c + 1;
    }
    a := a + 1;
  }
  var x: int;
  x := 0;
  while(x < b)
    decreases b - x;
    invariant true
      && 0 <= x
      && x <= b
      && (forall x₂₀: int ::
            (  0 <= x₂₀
              && x₂₀ < x
               ==> x₂₀ < b));
  {
    assert 0 <= bb[x];
    x := x + 1;
  }
  x := 0;
  while(x < c)
    decreases c - x;
    invariant true
      && 0 <= x
      && x <= c
      && (forall x₂₂: int ::
            (  0 <= x₂₂
              && x₂₂ < x
               ==> x₂₂ < c));
  {
    assert cc[x] < 0;
    x := x + 1;
  }
  c#result := 0;
  return;
}

