data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

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
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> (exists nondet_int₁₆: int, nondet_int₂₇: int, nondet_int₃₈: int ::
                      -2147483648 <= nondet_int₃₈
                      && nondet_int₃₈ < 2147483648
                      && -2147483648 <= nondet_int₂₇
                      && nondet_int₂₇ < 2147483648
                      && -2147483648 <= nondet_int₁₆
                      && nondet_int₁₆ < 2147483648
                      && i₉ < 200000
                      && a1[i₉] == nondet_int₁₆
                      && a2[i₉] == nondet_int₂₇
                      && a3[i₉] == nondet_int₃₈)))
      && (forall i₉: int ::
            (!(  old(i) <= i₉
              && i₉ < i
            )
               ==> a1[i₉] == old(a1)[i₉]
                && a2[i₉] == old(a2)[i₉]
                && a3[i₉] == old(a3)[i₉]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a1[i] := nondet_int₁;
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    a2[i] := nondet_int₂;
    var nondet_int₃: int;
    assume -2147483648 <= nondet_int₃ && nondet_int₃ < 2147483648;
    a3[i] := nondet_int₃;
    i := i + 1;
  }
  i := 0;
  while(i < 200000)
    decreases 200000 - i;
    invariant old(i) <= i
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ != z
                  && i₁₄ < 200000
                  && a2[i₁₄] == a1[i₁₄]
                ||   i₁₄ == z
                  && i₁₄ < 200000))
      && (forall i₁₄: int ::
            (!(  old(i) <= i₁₄
              && i₁₄ < i
            )
               ==> a2[i₁₄] == old(a2)[i₁₄]));
  {
    if(i != z) {
      a2[i] := a1[i];
    }
    i := i + 1;
  }
  i := 0;
  while(i < 200000)
    decreases 200000 - i;
    invariant old(i) <= i
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ != z
                  && i₁₇ < 200000
                  && a3[i₁₇] == a2[i₁₇]
                ||   i₁₇ == z
                  && i₁₇ < 200000
                  && a3[i₁₇] == a1[i₁₇]))
      && (forall i₁₇: int ::
            (!(  old(i) <= i₁₇
              && i₁₇ < i
            )
               ==> a3[i₁₇] == old(a3)[i₁₇]));
  {
    if(i != z) {
      a3[i] := a2[i];
    } else {
      a3[i] := a1[i];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 200000)
    decreases 200000 - x;
    invariant old(x) <= x
      && (forall x₂₁: int ::
            (  old(x) <= x₂₁
              && x₂₁ < x
               ==> x₂₁ < 200000));
  {
    assert a1[x] == a3[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

