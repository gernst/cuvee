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
    invariant true
      && old(j) <= j
      && j <= 100000
      && (forall x₅: int ::
            ((exists j₄: int ::
                    x₅ == j₄
                    && old(j) <= j₄
                    && j₄ < j)
               ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                      j₄ < 100000
                      && x₅ == j₄
                      && old(j) <= j₄
                      && j₄ < j
                      && src[x₅] == __VERIFIER_nondet_int₁₃)))
      && (forall x₅: int ::
            (!((exists j₄: int ::
                    x₅ == j₄
                    && old(j) <= j₄
                    && j₄ < j)
            )
               ==> src[x₅] == old(src[x₅])))
      && (forall j₄: int ::
            (  old(j₄) <= j₄
              && old(j) <= j₄
              && j₄ < j
               ==> j₄ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    src := src[j := __VERIFIER_nondet_int₁];
    j := j + 1;
  }
  while(i < 100000 && src[i] != 0)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₉: int ::
            ((exists i₈: int ::
                    x₉ == i₈
                    && old(i) <= i₈
                    && i₈ < i)
               ==> (exists i₈: int ::
                      i₈ < 100000
                      && src[i₈] != 0
                      && x₉ == i₈
                      && old(i) <= i₈
                      && i₈ < i
                      && dst[x₉] == src[i₈])))
      && (forall x₉: int ::
            (!((exists i₈: int ::
                    x₉ == i₈
                    && old(i) <= i₈
                    && i₈ < i)
            )
               ==> dst[x₉] == old(dst[x₉])))
      && (forall i₈: int ::
            (  old(i₈) <= i₈
              && old(i) <= i₈
              && i₈ < i
               ==> i₈ < 100000
                && src[i₈] != 0));
  {
    dst := dst[i := src[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < i)
    decreases i - x;
    invariant true
      && old(x) <= x
      && x <= i
      && (forall x₁₃: int ::
            (  old(x₁₃) <= x₁₃
              && old(x) <= x₁₃
              && x₁₃ < x
               ==> x₁₃ < i));
  {
    assert dst[x] == src[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

