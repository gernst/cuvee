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
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₅: int ::
            ((exists i₄: int ::
                    x₅ == i₄
                    && old(i) <= i₄
                    && i₄ < i)
               ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                      i₄ < 100000
                      && x₅ == i₄
                      && old(i) <= i₄
                      && i₄ < i
                      && src[x₅] == __VERIFIER_nondet_int₁₃)))
      && (forall x₅: int ::
            (!((exists i₄: int ::
                    x₅ == i₄
                    && old(i) <= i₄
                    && i₄ < i)
            )
               ==> src[x₅] == old(src[x₅])))
      && (forall i₄: int ::
            (  old(i₄) <= i₄
              && old(i) <= i₄
              && i₄ < i
               ==> i₄ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    src := src[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(src[i] != 0)
    invariant true
      && old(i) <= i
      && (forall x₉: int ::
            ((exists i₈: int ::
                    x₉ == i₈
                    && old(i) <= i₈
                    && i₈ < i)
               ==> (exists i₈: int ::
                      src[i₈] != 0
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
               ==> src[i₈] != 0));
  {
    dst := dst[i := src[i]];
    i := i + 1;
  }
  i := 0;
  while(src[i] != 0)
    invariant true
      && old(i) <= i
      && (forall i₁₂: int ::
            (  old(i₁₂) <= i₁₂
              && old(i) <= i₁₂
              && i₁₂ < i
               ==> src[i₁₂] != 0));
  {
    assert dst[i] == src[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

