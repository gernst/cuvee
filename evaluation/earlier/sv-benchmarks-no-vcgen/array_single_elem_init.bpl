data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₈: int ::
            (  (exists i₇: int ::
                    if(x₈ == i₇) then 0 <= i₇ && i₇ < i else x₈ == i₇ && 0 <= i₇ && i₇ < i)
              && (exists i₇: int ::
                      x₈ == i₇
                      && 0 <= i₇
                      && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇ := i₇ % 2][i₇] == 0
                        && a[i₇ := 0][i₇ := 1][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ == 0
                        && i₇ < 100000
                        && if(x₈ == i₇) then 0 <= i₇ && i₇ < i && a[x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i && a[x₈] == 0)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇] == 0
                        && a[i₇ := 0][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ != 0
                        && i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && a[x₈] == 0)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇ := i₇ % 2][i₇] != 0
                        && a[i₇ := 0][i₇ := 1][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ == 0
                        && i₇ < 100000
                        && if(x₈ == i₇) then 0 <= i₇ && i₇ < i && a[x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i && a[x₈] == 0)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇] != 0
                        && a[i₇ := 0][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ != 0
                        && i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && a[x₈] == 0)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        a[i₇ := 0][i₇ := 1][i₇] == 0
                        && __VERIFIER_nondet_int₁₅ == 0
                        && i₇ < 100000
                        && if(x₈ == i₇) then 0 <= i₇ && i₇ < i && a[x₈] == 1 else x₈ == i₇ && 0 <= i₇ && i₇ < i && a[x₈] == 0)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        a[i₇ := 0][i₇] == 0
                        && __VERIFIER_nondet_int₁₅ != 0
                        && i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && a[x₈] == 0)))
      && (forall x₈: int ::
            (!(  (exists i₇: int ::
                    if(x₈ == i₇) then 0 <= i₇ && i₇ < i else x₈ == i₇ && 0 <= i₇ && i₇ < i)
              && (exists i₇: int ::
                      x₈ == i₇
                      && 0 <= i₇
                      && i₇ < i)
            )
               ==> a[x₈] == old(a[x₈])))
      && (forall x₉: int ::
            ((exists i₇: int ::
                    x₉ == i₇
                    && 0 <= i₇
                    && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇ := i₇ % 2][i₇] == 0
                        && a[i₇ := 0][i₇ := 1][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ == 0
                        && i₇ < 100000
                        && x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && b[x₉] == i₇ % 2)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇ := i₇ % 2][i₇] != 0
                        && a[i₇ := 0][i₇ := 1][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ == 0
                        && i₇ < 100000
                        && x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && b[x₉] == i₇ % 2)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        a[i₇ := 0][i₇ := 1][i₇] == 0
                        && __VERIFIER_nondet_int₁₅ == 0
                        && i₇ < 100000
                        && x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && b[x₉] == i₇ % 2)))
      && (forall x₉: int ::
            (!((exists i₇: int ::
                    x₉ == i₇
                    && 0 <= i₇
                    && i₇ < i)
            )
               ==> b[x₉] == old(b[x₉])))
      && (forall x₁₀: int ::
            ((exists i₇: int ::
                    x₁₀ == i₇
                    && 0 <= i₇
                    && i₇ < i)
               ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇ := i₇ % 2][i₇] == 0
                        && a[i₇ := 0][i₇ := 1][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ == 0
                        && i₇ < 100000
                        && x₁₀ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && c[x₁₀] == 0)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇] == 0
                        && a[i₇ := 0][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ != 0
                        && i₇ < 100000
                        && x₁₀ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && c[x₁₀] == 0)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇ := i₇ % 2][i₇] != 0
                        && a[i₇ := 0][i₇ := 1][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ == 0
                        && i₇ < 100000
                        && x₁₀ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && c[x₁₀] == 1)
                || (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        b[i₇] != 0
                        && a[i₇ := 0][i₇] != 0
                        && __VERIFIER_nondet_int₁₅ != 0
                        && i₇ < 100000
                        && x₁₀ == i₇
                        && 0 <= i₇
                        && i₇ < i
                        && c[x₁₀] == 1)))
      && (forall x₁₀: int ::
            (!((exists i₇: int ::
                    x₁₀ == i₇
                    && 0 <= i₇
                    && i₇ < i)
            )
               ==> c[x₁₀] == old(c[x₁₀])))
      && (forall i₇: int ::
            (  0 <= i₇
              && i₇ < i
               ==> i₇ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    var q: int;
    q := __VERIFIER_nondet_int₁;
    a := a[i := 0];
    if(q == 0) {
      a := a[i := 1];
      b := b[i := i % 2];
    }
    if(a[i] != 0) {
      if(b[i] == 0) {
        c := c[i := 0];
      } else {
        c := c[i := 1];
      }
    }
    i := i + 1;
  }
  a := a[15000 := 1];
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall i₁₅: int ::
            (  0 <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < 100000));
  {
    if(i == 15000) {
      assert c[i] == 0;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

