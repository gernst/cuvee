data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

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
      && (forall j₄: int ::
            (  old(j) <= j₄
              && j₄ < j
               ==> (exists nondet_int₁₃: int ::
                      -2147483648 <= nondet_int₁₃
                      && nondet_int₁₃ < 2147483648
                      && j₄ < 100000
                      && src[j₄] == nondet_int₁₃)))
      && (forall j₄: int ::
            (!(  old(j) <= j₄
              && j₄ < j
            )
               ==> src[j₄] == old(src)[j₄]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    src[j] := nondet_int₁;
    j := j + 1;
  }
  while(i < 100000 && src[i] != 0)
    decreases 100000 - i;
    invariant old(i) <= i
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
    dst[i] := src[i];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < i)
    decreases i - x;
    invariant old(x) <= x
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

