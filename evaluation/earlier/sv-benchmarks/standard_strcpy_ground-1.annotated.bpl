data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var src: [int]int;
  var dst: [int]int;
  var i: int := 0;
  var j: int := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant old(j) <= j
      && j <= 100000
      && (forall j₄: int ::
            (  old(j) <= j₄
              && j₄ < j
               ==> (exists __VERIFIER_nondet_int₁₃: int ::
                      j₄ < 100000
                      && src[j₄] == __VERIFIER_nondet_int₁₃)))
      && (forall j₄: int ::
            (!(  old(j) <= j₄
              && j₄ < j
            )
               ==> src[j₄] == old(src)[j₄]));
  {
    var __VERIFIER_nondet_int₁: int;
    src := src[j := __VERIFIER_nondet_int₁];
    j := j + 1;
  }
  while(i < 100000 && src[i] != 0)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ < 100000
                && src[i₇] != 0
                && dst[i₇] == src[i₇]))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> dst[i₇] == old(dst)[i₇]));
  {
    dst := dst[i := src[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < i)
    decreases i - x;
    invariant old(x) <= x
      && x <= i
      && (forall x₁₁: int ::
            (  old(x) <= x₁₁
              && x₁₁ < x
               ==> x₁₁ < i));
  {
    assert dst[x] == src[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

