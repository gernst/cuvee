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
    invariant old(i) <= i
      && i <= 100000
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> (exists __VERIFIER_nondet_int₁₄: int ::
                      i₅ < 100000
                      && aa[i₅] == __VERIFIER_nondet_int₁₄)))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> aa[i₅] == old(aa)[i₅]));
  {
    var __VERIFIER_nondet_int₁: int;
    aa := aa[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  while(a < 100000)
    decreases 100000 - a;
    invariant old(c) <= c
      && old(a) <= a
      && old(b) <= b
      && a <= 100000
      && (forall c₈: int, a₉: int, b₁₀: int ::
            (  old(c) <= c₈
              && c₈ < c
              && old(a) <= a₉
              && a₉ < a
              && old(b) <= b₁₀
              && b₁₀ < b
               ==> 0 <= aa[a₉]
                  && a₉ < 100000
                  && bb[b₁₀] == aa[a₉]
                ||   !(0 <= aa[a₉]
                  )
                  && a₉ < 100000
                  && cc[c₈] == aa[a₉]))
      && (forall c₈: int, a₉: int, b₁₀: int ::
            (!(  old(c) <= c₈
              && c₈ < c
              && old(a) <= a₉
              && a₉ < a
              && old(b) <= b₁₀
              && b₁₀ < b
            )
               ==> bb[b₁₀] == old(bb)[b₁₀]
                && cc[c₈] == old(cc)[c₈]));
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
    invariant old(x) <= x
      && x <= b
      && (forall x₁₇: int ::
            (  old(x) <= x₁₇
              && x₁₇ < x
               ==> x₁₇ < b));
  {
    assert 0 <= bb[x];
    x := x + 1;
  }
  x := 0;
  while(x < c)
    decreases c - x;
    invariant old(x) <= x
      && x <= c
      && (forall x₁₉: int ::
            (  old(x) <= x₁₉
              && x₁₉ < x
               ==> x₁₉ < c));
  {
    assert cc[x] < 0;
    x := x + 1;
  }
  c#result := 0;
  return;
}

