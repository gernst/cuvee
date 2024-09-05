data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a1: [int]int;
  var a2: [int]int;
  var a3: [int]int;
  var i: int;
  var z: int;
  z := 150000;
  i := 0;
  while(i < 200000)
    decreases 200000 - i;
    invariant true
      && old(i) <= i
      && i <= 200000
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists __VERIFIER_nondet_int₁₆: int, i₉: int ::
                      i₉ < 200000
                      && x₁₀ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && a1[x₁₀] == __VERIFIER_nondet_int₁₆)))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> a1[x₁₀] == old(a1[x₁₀])))
      && (forall x₁₁: int ::
            ((exists i₉: int ::
                    x₁₁ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists __VERIFIER_nondet_int₂₇: int, i₉: int ::
                      i₉ < 200000
                      && x₁₁ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && a2[x₁₁] == __VERIFIER_nondet_int₂₇)))
      && (forall x₁₁: int ::
            (!((exists i₉: int ::
                    x₁₁ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> a2[x₁₁] == old(a2[x₁₁])))
      && (forall x₁₂: int ::
            ((exists i₉: int ::
                    x₁₂ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists __VERIFIER_nondet_int₃₈: int, i₉: int ::
                      i₉ < 200000
                      && x₁₂ == i₉
                      && old(i) <= i₉
                      && i₉ < i
                      && a3[x₁₂] == __VERIFIER_nondet_int₃₈)))
      && (forall x₁₂: int ::
            (!((exists i₉: int ::
                    x₁₂ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> a3[x₁₂] == old(a3[x₁₂])))
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < 200000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[i := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a2 := a2[i := __VERIFIER_nondet_int₂];
    var __VERIFIER_nondet_int₃: int;
    a3 := a3[i := __VERIFIER_nondet_int₃];
    i := i + 1;
  }
  i := 0;
  while(i < 200000)
    decreases 200000 - i;
    invariant true
      && old(i) <= i
      && i <= 200000
      && (forall x₁₈: int ::
            ((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
               ==> (exists i₁₇: int ::
                      i₁₇ != z
                      && i₁₇ < 200000
                      && x₁₈ == i₁₇
                      && old(i) <= i₁₇
                      && i₁₇ < i
                      && a2[x₁₈] == a1[i₁₇])))
      && (forall x₁₈: int ::
            (!((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
            )
               ==> a2[x₁₈] == old(a2[x₁₈])))
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < 200000));
  {
    if(i != z) {
      a2 := a2[i := a1[i]];
    }
    i := i + 1;
  }
  i := 0;
  while(i < 200000)
    decreases 200000 - i;
    invariant true
      && old(i) <= i
      && i <= 200000
      && (forall x₂₂: int ::
            ((exists i₂₁: int ::
                    x₂₂ == i₂₁
                    && old(i) <= i₂₁
                    && i₂₁ < i)
               ==> (exists i₂₁: int ::
                        i₂₁ != z
                        && i₂₁ < 200000
                        && x₂₂ == i₂₁
                        && old(i) <= i₂₁
                        && i₂₁ < i
                        && a3[x₂₂] == a2[i₂₁])
                || (exists i₂₁: int ::
                        i₂₁ == z
                        && i₂₁ < 200000
                        && x₂₂ == i₂₁
                        && old(i) <= i₂₁
                        && i₂₁ < i
                        && a3[x₂₂] == a1[i₂₁])))
      && (forall x₂₂: int ::
            (!((exists i₂₁: int ::
                    x₂₂ == i₂₁
                    && old(i) <= i₂₁
                    && i₂₁ < i)
            )
               ==> a3[x₂₂] == old(a3[x₂₂])))
      && (forall i₂₁: int ::
            (  old(i) <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < 200000));
  {
    if(i != z) {
      a3 := a3[i := a2[i]];
    } else {
      a3 := a3[i := a1[i]];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 200000)
    decreases 200000 - x;
    invariant true
      && old(x) <= x
      && x <= 200000
      && (forall x₂₆: int ::
            (  old(x) <= x₂₆
              && x₂₆ < x
               ==> x₂₆ < 200000));
  {
    assert a1[x] == a3[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

