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
    invariant old(b) <= b
      && old(a) <= a
      && (forall b₈: int, a₉: int ::
            (  old(b) <= b₈
              && b₈ < b
              && old(a) <= a₉
              && a₉ < a
               ==> 0 <= aa[a₉]
                  && a₉ < 100000
                  && bb[b₈] == aa[a₉]
                ||   !(0 <= aa[a₉]
                  )
                  && a₉ < 100000))
      && (forall b₈: int, a₉: int ::
            (!(  old(b) <= b₈
              && b₈ < b
              && old(a) <= a₉
              && a₉ < a
            )
               ==> bb[b₈] == old(bb)[b₈]));
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
    invariant old(c) <= c
      && old(a) <= a
      && (forall c₁₃: int, a₁₄: int ::
            (  old(c) <= c₁₃
              && c₁₃ < c
              && old(a) <= a₁₄
              && a₁₄ < a
               ==> aa[a₁₄] < 0
                  && a₁₄ < 100000
                  && cc[c₁₃] == aa[a₁₄]
                ||   !(aa[a₁₄] < 0
                  )
                  && a₁₄ < 100000))
      && (forall c₁₃: int, a₁₄: int ::
            (!(  old(c) <= c₁₃
              && c₁₃ < c
              && old(a) <= a₁₄
              && a₁₄ < a
            )
               ==> cc[c₁₃] == old(cc)[c₁₃]));
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
    invariant old(x) <= x
      && (forall x₁₉: int ::
            (  old(x) <= x₁₉
              && x₁₉ < x
               ==> x₁₉ < b));
  {
    assert 0 <= bb[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

