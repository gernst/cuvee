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
  while(i < 10000)
    decreases 10000 - i;
    invariant true
      && old(i) <= i
      && i <= 10000
      && (forall x₅: int ::
            ((exists i₄: int ::
                    x₅ == i₄
                    && old(i) <= i₄
                    && i₄ < i)
               ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                      i₄ < 10000
                      && x₅ == i₄
                      && old(i) <= i₄
                      && i₄ < i
                      && b[x₅] == __VERIFIER_nondet_int₁₃)))
      && (forall x₅: int ::
            (!((exists i₄: int ::
                    x₅ == i₄
                    && old(i) <= i₄
                    && i₄ < i)
            )
               ==> b[x₅] == old(b[x₅])))
      && (forall i₄: int ::
            (  old(i₄) <= i₄
              && old(i) <= i₄
              && i₄ < i
               ==> i₄ < 10000));
  {
    var __VERIFIER_nondet_int₁: int;
    b := b[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 1;
  while(i < 10000)
    decreases 10000 - i;
    invariant true
      && old(j) <= j
      && i <= 10000
      && (forall x₁₀: int ::
            ((exists j₉: int ::
                    x₁₀ == j₉
                    && old(j) <= j₉
                    && j₉ < j)
               ==> (exists i₈: int, j₉: int ::
                      i₈ < 10000
                      && x₁₀ == j₉
                      && old(j) <= j₉
                      && j₉ < j
                      && a[x₁₀] == b[i₈])))
      && (forall x₁₀: int ::
            (!((exists j₉: int ::
                    x₁₀ == j₉
                    && old(j) <= j₉
                    && j₉ < j)
            )
               ==> a[x₁₀] == old(a[x₁₀])))
      && (forall i₈: int, j₉: int ::
            (  old(j₉) <= j₉
              && old(j) <= j₉
              && j₉ < j
               ==> i₈ < 10000));
  {
    a := a[j := b[i]];
    i := i + 6;
    j := j + 1;
  }
  i := 1;
  j := 0;
  while(i < 10000)
    decreases 10000 - i;
    invariant true
      && old(j) <= j
      && i <= 10000
      && (forall i₁₄: int, j₁₅: int ::
            (  old(j₁₅) <= j₁₅
              && old(j) <= j₁₅
              && j₁₅ < j
               ==> i₁₄ < 10000));
  {
    assert a[j] == b[6 * j + 1];
    i := i + 6;
    j := j + 1;
  }
  c#result := 0;
  return;
}

