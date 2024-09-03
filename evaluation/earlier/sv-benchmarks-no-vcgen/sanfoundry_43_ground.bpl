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
      && 0 <= i
      && i <= 100000
      && (forall x₃: int ::
            ((exists i₂: int ::
                    x₃ == i₂
                    && 0 <= i₂
                    && i₂ < i)
               ==> (exists i₂: int ::
                      i₂ < 100000
                      && x₃ == i₂
                      && 0 <= i₂
                      && i₂ < i
                      && dst[x₃] == 1 + src[i₂])))
      && (forall x₃: int ::
            (!((exists i₂: int ::
                    x₃ == i₂
                    && 0 <= i₂
                    && i₂ < i)
            )
               ==> dst[x₃] == old(dst[x₃])))
      && (forall i₂: int ::
            (  0 <= i₂
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
      && 0 <= i
      && i <= 100000
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && 0 <= i₉
                    && i₉ < i)
               ==> (exists __VERIFIER_nondet_int₂₈: int, i₉: int ::
                      i₉ < 100000
                      && x₁₀ == i₉
                      && 0 <= i₉
                      && i₉ < i
                      && src[x₁₀] == __VERIFIER_nondet_int₂₈)))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && 0 <= i₉
                    && i₉ < i)
            )
               ==> src[x₁₀] == old(src[x₁₀])))
      && (forall i₉: int ::
            (  0 <= i₉
              && i₉ < i
               ==> i₉ < 100000));
  {
    var __VERIFIER_nondet_int₂: int;
    src := src[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  var incrementArray₄: c#void;
  {
    var src: [int]int, dst: [int]int := src, dst;
    havoc incrementArray₄;
    {
      var i: int;
      i := 0;
      while(i < 100000)
        decreases 100000 - i;
        invariant true
          && 0 <= i
          && i <= 100000
          && (forall x₁₇: int ::
                ((exists i₁₆: int ::
                        x₁₇ == i₁₆
                        && 0 <= i₁₆
                        && i₁₆ < i)
                   ==> (exists i₁₆: int ::
                          i₁₆ < 100000
                          && x₁₇ == i₁₆
                          && 0 <= i₁₆
                          && i₁₆ < i
                          && dst[x₁₇] == 1 + src[i₁₆])))
          && (forall x₁₇: int ::
                (!((exists i₁₆: int ::
                        x₁₇ == i₁₆
                        && 0 <= i₁₆
                        && i₁₆ < i)
                )
                   ==> dst[x₁₇] == old(dst[x₁₇])))
          && (forall i₁₆: int ::
                (  0 <= i₁₆
                  && i₁₆ < i
                   ==> i₁₆ < 100000));
      {
        dst := dst[i := src[i] + 1];
        i := i + 1;
      }
    }
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₂₂: int ::
            ((exists x₂₁: int ::
                    x₂₂ == x₂₁
                    && 0 <= x₂₁
                    && x₂₁ < x)
               ==> (exists x₂₁: int ::
                      x₂₁ < 100000
                      && x₂₂ == x₂₁
                      && 0 <= x₂₁
                      && x₂₁ < x
                      && src[x₂₂] == -1 + dst[x₂₁])))
      && (forall x₂₂: int ::
            (!((exists x₂₁: int ::
                    x₂₂ == x₂₁
                    && 0 <= x₂₁
                    && x₂₁ < x)
            )
               ==> src[x₂₂] == old(src[x₂₂])))
      && (forall x₂₁: int ::
            (  0 <= x₂₁
              && x₂₁ < x
               ==> x₂₁ < 100000));
  {
    src := src[x := dst[x] - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}

