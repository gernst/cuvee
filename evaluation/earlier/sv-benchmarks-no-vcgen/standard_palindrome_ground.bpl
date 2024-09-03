data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var A: [int]int;
  var i: int;
  i := 0;
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
                      && A[x₅] == __VERIFIER_nondet_int₁₃)))
      && (forall x₅: int ::
            (!((exists i₄: int ::
                    x₅ == i₄
                    && 0 <= i₄
                    && i₄ < i)
            )
               ==> A[x₅] == old(A[x₅])))
      && (forall i₄: int ::
            (  0 <= i₄
              && i₄ < i
               ==> i₄ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    A := A[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(i < 100000 / 2)
    decreases 100000 / 2 - i;
    invariant true
      && 0 <= i
      && i <= 100000 / 2
      && (forall x₉: int ::
            ((exists i₈: int ::
                    x₉ == i₈
                    && 0 <= i₈
                    && i₈ < i)
               ==> (exists i₈: int ::
                      i₈ < 100000 / 2
                      && x₉ == i₈
                      && 0 <= i₈
                      && i₈ < i
                      && A[x₉] == old(A)[99999 + -i₈])))
      && (forall x₉: int ::
            (!((exists i₈: int ::
                    x₉ == i₈
                    && 0 <= i₈
                    && i₈ < i)
            )
               ==> A[x₉] == old(A[x₉])))
      && (forall i₈: int ::
            (  0 <= i₈
              && i₈ < i
               ==> i₈ < 100000 / 2));
  {
    A := A[i := A[100000 - i - 1]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000 / 2)
    decreases 100000 / 2 - x;
    invariant true
      && 0 <= x
      && x <= 100000 / 2
      && (forall x₁₃: int ::
            (  0 <= x₁₃
              && x₁₃ < x
               ==> x₁₃ < 100000 / 2));
  {
    assert A[x] == A[100000 - x - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}

