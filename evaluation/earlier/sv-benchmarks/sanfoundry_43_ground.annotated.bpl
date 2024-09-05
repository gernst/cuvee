data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure incrementArray(src: [int]int, dst: [int]int)
  returns (c#result: c#void)
{
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₃: int ::
            ((exists i₂: int ::
                    x₃ == i₂
                    && old(i) <= i₂
                    && i₂ < i)
               ==> (exists i₂: int ::
                      i₂ < 100000
                      && x₃ == i₂
                      && old(i) <= i₂
                      && i₂ < i
                      && dst[x₃] == 1 + src[i₂])))
      && (forall x₃: int ::
            (!((exists i₂: int ::
                    x₃ == i₂
                    && old(i) <= i₂
                    && i₂ < i)
            )
               ==> dst[x₃] == old(dst[x₃])))
      && (forall i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> i₂ < 100000));
  {
    dst := dst[i := src[i] + 1];
    i := i + 1;
  }
}

procedure main()
  returns (c#result: int)
{
  var src: [int]int;
  var dst: [int]int;
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
               ==> (exists __VERIFIER_nondet_int₂₈: int, i₉: int ::
                      i₉ < 100000
                      && x₁₀ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && src[x₁₀] == __VERIFIER_nondet_int₂₈)))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> src[x₁₀] == old(src[x₁₀])))
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < 100000));
  {
    var __VERIFIER_nondet_int₂: int;
    src := src[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  var incrementArray₄: c#void;
  incrementArray₄ := call incrementArray(src, dst);
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₁₆: int ::
            ((exists x₁₅: int ::
                    x₁₆ == x₁₅
                    && old(x) <= x₁₅
                    && x₁₅ < x)
               ==> (exists x₁₅: int ::
                      x₁₅ < 100000
                      && x₁₆ == x₁₅
                      && old(x) <= x₁₅
                      && x₁₅ < x
                      && src[x₁₆] == -1 + dst[x₁₅])))
      && (forall x₁₆: int ::
            (!((exists x₁₅: int ::
                    x₁₆ == x₁₅
                    && old(x) <= x₁₅
                    && x₁₅ < x)
            )
               ==> src[x₁₆] == old(src[x₁₆])))
      && (forall x₁₅: int ::
            (  old(x) <= x₁₅
              && x₁₅ < x
               ==> x₁₅ < 100000));
  {
    src := src[x := dst[x] - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}

