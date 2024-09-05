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
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
               ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                      i₅ < 100000
                      && x₆ == i₅
                      && old(i) <= i₅
                      && i₅ < i
                      && aa[x₆] == __VERIFIER_nondet_int₁₄)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
            )
               ==> aa[x₆] == old(aa[x₆])))
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    aa := aa[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && old(c) <= c
      && old(a) <= a
      && old(b) <= b
      && a <= 100000
      && (forall x₁₂: int ::
            ((exists c₉: int ::
                    x₁₂ == c₉
                    && old(c) <= c₉
                    && c₉ < c)
               ==> (exists c₉: int, a₁₀: int ::
                      !(0 <= aa[a₁₀]
                      )
                      && a₁₀ < 100000
                      && x₁₂ == c₉
                      && old(c) <= c₉
                      && c₉ < c
                      && cc[x₁₂] == aa[a₁₀])))
      && (forall x₁₂: int ::
            (!((exists c₉: int ::
                    x₁₂ == c₉
                    && old(c) <= c₉
                    && c₉ < c)
            )
               ==> cc[x₁₂] == old(cc[x₁₂])))
      && (forall x₁₃: int ::
            ((exists b₁₁: int ::
                    x₁₃ == b₁₁
                    && old(b) <= b₁₁
                    && b₁₁ < b)
               ==> (exists a₁₀: int, b₁₁: int ::
                      0 <= aa[a₁₀]
                      && a₁₀ < 100000
                      && x₁₃ == b₁₁
                      && old(b) <= b₁₁
                      && b₁₁ < b
                      && bb[x₁₃] == aa[a₁₀])))
      && (forall x₁₃: int ::
            (!((exists b₁₁: int ::
                    x₁₃ == b₁₁
                    && old(b) <= b₁₁
                    && b₁₁ < b)
            )
               ==> bb[x₁₃] == old(bb[x₁₃])))
      && (forall c₉: int, a₁₀: int, b₁₁: int ::
            (  old(c) <= c₉
              && c₉ < c
              && old(a) <= a₁₀
              && a₁₀ < a
              && old(b) <= b₁₁
              && b₁₁ < b
               ==> a₁₀ < 100000));
  {
    if(0 <= aa[a]) {
      bb := bb[b := aa[a]];
      b := b + 1;
    } else {
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
      && old(x) <= x
      && x <= b
      && (forall x₂₀: int ::
            (  old(x) <= x₂₀
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
      && old(x) <= x
      && x <= c
      && (forall x₂₂: int ::
            (  old(x) <= x₂₂
              && x₂₂ < x
               ==> x₂₂ < c));
  {
    assert cc[x] < 0;
    x := x + 1;
  }
  c#result := 0;
  return;
}

