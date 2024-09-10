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
  var a: [int]int;
  var b: [int]int;
  var i: int := 0;
  var j: int := 0;
  while(i < 10000)
    decreases 10000 - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> (exists nondet_int₁₃: int ::
                      -2147483648 <= nondet_int₁₃
                      && nondet_int₁₃ < 2147483648
                      && i₄ < 10000
                      && b[i₄] == nondet_int₁₃)))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> b[i₄] == old(b)[i₄]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    b[i] := nondet_int₁;
    i := i + 1;
  }
  i := 0;
  while(i < 10000)
    decreases 10000 - i;
    invariant i + old(i) == j + old(j)
      && old(i) <= i
      && old(j) <= j
      && (forall i₇: int, j₈: int ::
            (  i₇ + old(i₇) == old(j₈) + j₈
              && old(i) <= i₇
              && i₇ < i
              && old(j) <= j₈
              && j₈ < j
               ==> i₇ < 10000
                && a[j₈] == b[i₇]))
      && (forall i₇: int, j₈: int ::
            (  i₇ + old(i₇) == old(j₈) + j₈
              && !(  old(i) <= i₇
                && i₇ < i
                && old(j) <= j₈
                && j₈ < j
              )
               ==> a[j₈] == old(a)[j₈]));
  {
    a[j] := b[i];
    i := i + 1;
    j := j + 1;
  }
  i := 0;
  j := 0;
  while(i < 10000)
    decreases 10000 - i;
    invariant i + old(i) == j + old(j)
      && old(i) <= i
      && old(j) <= j
      && (forall i₁₂: int, j₁₃: int ::
            (  old(i₁₂) + i₁₂ == old(j₁₃) + j₁₃
              && old(i) <= i₁₂
              && i₁₂ < i
              && old(j) <= j₁₃
              && j₁₃ < j
               ==> i₁₂ < 10000));
  {
    assert a[j] == b[j];
    i := i + 1;
    j := j + 1;
  }
  c#result := 0;
  return;
}

