data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

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
    dst[i] := src[i] + 1;
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
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> (exists nondet_int₂₇: int ::
                      -2147483648 <= nondet_int₂₇
                      && nondet_int₂₇ < 2147483648
                      && i₈ < 100000
                      && src[i₈] == nondet_int₂₇)))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> src[i₈] == old(src)[i₈]));
  {
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    src[i] := nondet_int₂;
    i := i + 1;
  }
  var incrementArray₄: c#void;
  incrementArray₄ := call incrementArray(src, dst);
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
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
    src[x] := dst[x] - 1;
    x := x + 1;
  }
  c#result := 0;
  return;
}

