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
      && old(b) <= b
      && old(a) <= a
      && a <= 100000
      && (forall x₁₁: int ::
            ((exists b₉: int ::
                    x₁₁ == b₉
                    && old(b) <= b₉
                    && b₉ < b)
               ==> (exists b₉: int, a₁₀: int ::
                      0 <= aa[a₁₀]
                      && a₁₀ < 100000
                      && x₁₁ == b₉
                      && old(b) <= b₉
                      && b₉ < b
                      && bb[x₁₁] == aa[a₁₀])))
      && (forall x₁₁: int ::
            (!((exists b₉: int ::
                    x₁₁ == b₉
                    && old(b) <= b₉
                    && b₉ < b)
            )
               ==> bb[x₁₁] == old(bb[x₁₁])))
      && (forall b₉: int, a₁₀: int ::
            (  old(b) <= b₉
              && b₉ < b
              && old(a) <= a₁₀
              && a₁₀ < a
               ==> a₁₀ < 100000));
  {
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
      && old(c) <= c
      && old(a) <= a
      && a <= 100000
      && (forall x₁₇: int ::
            ((exists c₁₅: int ::
                    x₁₇ == c₁₅
                    && old(c) <= c₁₅
                    && c₁₅ < c)
               ==> (exists c₁₅: int, a₁₆: int ::
                      aa[a₁₆] < 0
                      && a₁₆ < 100000
                      && x₁₇ == c₁₅
                      && old(c) <= c₁₅
                      && c₁₅ < c
                      && cc[x₁₇] == aa[a₁₆])))
      && (forall x₁₇: int ::
            (!((exists c₁₅: int ::
                    x₁₇ == c₁₅
                    && old(c) <= c₁₅
                    && c₁₅ < c)
            )
               ==> cc[x₁₇] == old(cc[x₁₇])))
      && (forall c₁₅: int, a₁₆: int ::
            (  old(c) <= c₁₅
              && c₁₅ < c
              && old(a) <= a₁₆
              && a₁₆ < a
               ==> a₁₆ < 100000));
  {
    if(aa[a] < 0) {
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
      && (forall x₂₂: int ::
            (  old(x) <= x₂₂
              && x₂₂ < x
               ==> x₂₂ < b));
  {
    assert 0 <= bb[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

