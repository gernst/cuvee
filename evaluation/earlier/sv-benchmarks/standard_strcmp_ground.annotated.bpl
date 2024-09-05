data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure _strcmp(src: [int]int, dst: [int]int)
  returns (c#result: int)
{
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> i₂ < 100000
                && !(  dst[i₂] != src[i₂]
                  && i₂ < 100000
                )));
  {
    if(dst[i] != src[i]) {
      c#result := 1;
      return;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists __VERIFIER_nondet_int₁₇: int, i₉: int ::
                      i₉ < 100000
                      && x₁₀ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && a[x₁₀] == __VERIFIER_nondet_int₁₇)))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> a[x₁₀] == old(a[x₁₀])))
      && (forall x₁₁: int ::
            ((exists i₉: int ::
                    x₁₁ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists __VERIFIER_nondet_int₂₈: int, i₉: int ::
                      i₉ < 100000
                      && x₁₁ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && b[x₁₁] == __VERIFIER_nondet_int₂₈)))
      && (forall x₁₁: int ::
            (!((exists i₉: int ::
                    x₁₁ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> b[x₁₁] == old(b[x₁₁])))
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    b := b[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  var _strcmp₄: int;
  _strcmp₄ := call _strcmp(a, b);
  var c: int;
  c := _strcmp₄;
  if(c == 0) {
    var x: int;
    x := 0;
    while(x < 100000)
      decreases 100000 - x;
      invariant true
        && old(x) <= x
        && x <= 100000
        && (forall x₁₈: int ::
              (  old(x) <= x₁₈
                && x₁₈ < x
                 ==> x₁₈ < 100000));
    {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

