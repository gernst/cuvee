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
  var i: int;
  var z: int;
  z := 150000;
  i := 0;
  while(i < 200000)
    decreases 200000 - i;
    invariant true
      && old(i) <= i
      && i <= 200000
      && (forall x₈: int ::
            ((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                      i₇ < 200000
                      && x₈ == i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && a1[x₈] == __VERIFIER_nondet_int₁₅)))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> a1[x₈] == old(a1[x₈])))
      && (forall x₉: int ::
            ((exists i₇: int ::
                    x₉ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                      i₇ < 200000
                      && x₉ == i₇
                      && old(i) <= i₇
                      && i₇ < i
                      && a2[x₉] == __VERIFIER_nondet_int₂₆)))
      && (forall x₉: int ::
            (!((exists i₇: int ::
                    x₉ == i₇
                    && old(i) <= i₇
                    && i₇ < i)
            )
               ==> a2[x₉] == old(a2[x₉])))
      && (forall i₇: int ::
            (  old(i₇) <= i₇
              && old(i) <= i₇
              && i₇ < i
               ==> i₇ < 200000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[i := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a2 := a2[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < 200000)
    decreases 200000 - i;
    invariant true
      && old(i) <= i
      && i <= 200000
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
               ==> (exists i₁₃: int ::
                      i₁₃ != z
                      && i₁₃ < 200000
                      && x₁₄ == i₁₃
                      && old(i) <= i₁₃
                      && i₁₃ < i
                      && a2[x₁₄] == a1[i₁₃])))
      && (forall x₁₄: int ::
            (!((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
            )
               ==> a2[x₁₄] == old(a2[x₁₄])))
      && (forall i₁₃: int ::
            (  old(i₁₃) <= i₁₃
              && old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 200000));
  {
    if(i != z) {
      a2 := a2[i := a1[i]];
    }
    i := i + 1;
  }
  var x: int;
  z := 150001;
  x := 0;
  while(x < 200000)
    decreases 200000 - x;
    invariant true
      && old(x) <= x
      && x <= 200000
      && (forall x₁₈: int ::
            (  old(x₁₈) <= x₁₈
              && old(x) <= x₁₈
              && x₁₈ < x
               ==> x₁₈ < 200000));
  {
    if(x != z) {
      assert a1[x] == a2[x];
    }
    x := x + 1;
  }
  c#result := 0;
  return;
}

