data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var i: int := 0;
  var j: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₅: int ::
            ((exists i₄: int ::
                    x₅ == i₄
                    && 0 <= i₄
                    && i₄ < i)
               ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                      i₄ < 100000
                      && x₅ == i₄
                      && 0 <= i₄
                      && i₄ < i
                      && b[x₅] == __VERIFIER_nondet_int₁₃)))
      && (forall x₅: int ::
            (!((exists i₄: int ::
                    x₅ == i₄
                    && 0 <= i₄
                    && i₄ < i)
            )
               ==> b[x₅] == old(b[x₅])))
      && (forall i₄: int ::
            (  0 <= i₄
              && i₄ < i
               ==> i₄ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    b := b[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 1;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= j
      && i <= 100000
      && (forall x₁₀: int ::
            ((exists j₉: int ::
                    x₁₀ == j₉
                    && 0 <= j₉
                    && j₉ < j)
               ==> (exists i₈: int, j₉: int ::
                      i₈ < 100000
                      && x₁₀ == j₉
                      && 0 <= j₉
                      && j₉ < j
                      && a[x₁₀] == b[i₈])))
      && (forall x₁₀: int ::
            (!((exists j₉: int ::
                    x₁₀ == j₉
                    && 0 <= j₉
                    && j₉ < j)
            )
               ==> a[x₁₀] == old(a[x₁₀])))
      && (forall i₈: int, j₉: int ::
            (  0 <= j₉
              && j₉ < j
               ==> i₈ < 100000));
  {
    a := a[j := b[i]];
    i := i + 9;
    j := j + 1;
  }
  i := 1;
  j := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= j
      && i <= 100000
      && (forall i₁₄: int, j₁₅: int ::
            (  0 <= j₁₅
              && j₁₅ < j
               ==> i₁₄ < 100000));
  {
    assert a[j] == b[9 * j + 1];
    i := i + 9;
    j := j + 1;
  }
  c#result := 0;
  return;
}

