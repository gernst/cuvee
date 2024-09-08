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
    invariant old(i) <= i
      && i <= 100000
      && (forall i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> i₂ < 100000
                && dst[i₂] == 1 + src[i₂]))
      && (forall i₂: int ::
            (!(  old(i) <= i₂
              && i₂ < i
            )
               ==> dst[i₂] == old(dst)[i₂]));
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
    invariant old(i) <= i
      && i <= 100000
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> (exists __VERIFIER_nondet_int₂₇: int ::
                      i₈ < 100000
                      && src[i₈] == __VERIFIER_nondet_int₂₇)))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> src[i₈] == old(src)[i₈]));
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
    invariant old(x) <= x
      && x <= 100000
      && (forall x₁₃: int ::
            (  old(x) <= x₁₃
              && x₁₃ < x
               ==> x₁₃ < 100000
                && src[x₁₃] == -1 + dst[x₁₃]))
      && (forall x₁₃: int ::
            (!(  old(x) <= x₁₃
              && x₁₃ < x
            )
               ==> src[x₁₃] == old(src)[x₁₃]));
  {
    src := src[x := dst[x] - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}

