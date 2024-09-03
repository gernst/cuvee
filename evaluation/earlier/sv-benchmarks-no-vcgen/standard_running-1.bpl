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
                      && a[x₅] == __VERIFIER_nondet_int₁₃)))
      && (forall x₅: int ::
            (!((exists i₄: int ::
                    x₅ == i₄
                    && 0 <= i₄
                    && i₄ < i)
            )
               ==> a[x₅] == old(a[x₅])))
      && (forall i₄: int ::
            (  0 <= i₄
              && i₄ < i
               ==> i₄ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₉: int ::
            ((exists i₈: int ::
                    x₉ == i₈
                    && 0 <= i₈
                    && i₈ < i)
               ==> (exists i₈: int ::
                        0 <= a[i₈]
                        && i₈ < 100000
                        && x₉ == i₈
                        && 0 <= i₈
                        && i₈ < i
                        && b[x₉] == 1)
                || (exists i₈: int ::
                        !(0 <= a[i₈]
                        )
                        && i₈ < 100000
                        && x₉ == i₈
                        && 0 <= i₈
                        && i₈ < i
                        && b[x₉] == 0)))
      && (forall x₉: int ::
            (!((exists i₈: int ::
                    x₉ == i₈
                    && 0 <= i₈
                    && i₈ < i)
            )
               ==> b[x₉] == old(b[x₉])))
      && (forall i₈: int ::
            (  0 <= i₈
              && i₈ < i
               ==> i₈ < 100000));
  {
    if(0 <= a[i]) {
      b := b[i := 1];
    } else {
      b := b[i := 0];
    }
    i := i + 1;
  }
  var f: int := 1;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall i₁₃: int ::
            (  0 <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 100000));
  {
    if(0 <= a[i] && !(b[i] != 0)) {
      f := 0;
    }
    if(a[i] < 0 && !(b[i] != 0)) {
      f := 0;
    }
    i := i + 1;
  }
  assert f != 0;
  c#result := 0;
  return;
}

