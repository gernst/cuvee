data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var SIZE: int;

var MAX: int;

procedure main()
  returns (c#result: int)
  modifies SIZE, MAX;
{
  SIZE := 0;
  MAX := 100000;
  havoc SIZE;
  assume -2147483648 <= SIZE && SIZE < 2147483648;
  if(1 < SIZE && SIZE < MAX) {
    var i: int;
    var tmp: int;
    var a: [int]int;
    var b: [int]int;
    var a_copy: [int]int;
    var b_copy: [int]int;
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₁₀: int ::
              (  old(i) <= i₁₀
                && i₁₀ < i
                 ==> (exists nondet_int₁₈: int, nondet_int₂₉: int ::
                        -2147483648 <= nondet_int₂₉
                        && nondet_int₂₉ < 2147483648
                        && -2147483648 <= nondet_int₁₈
                        && nondet_int₁₈ < 2147483648
                        && i₁₀ < SIZE
                        && a_copy[i₁₀] == nondet_int₁₈
                        && b_copy[i₁₀] == nondet_int₂₉)))
        && (forall i₁₀: int ::
              (!(  old(i) <= i₁₀
                && i₁₀ < i
              )
                 ==> a_copy[i₁₀] == old(a_copy)[i₁₀]
                  && b_copy[i₁₀] == old(b_copy)[i₁₀]));
    {
      var nondet_int₁: int;
      assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
      a_copy[i] := nondet_int₁;
      var nondet_int₂: int;
      assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
      b_copy[i] := nondet_int₂;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₁₄: int ::
              (  old(i) <= i₁₄
                && i₁₄ < i
                 ==> i₁₄ < SIZE
                  && a[i₁₄] == a_copy[-1 + SIZE + -i₁₄]
                  && b[i₁₄] == b_copy[-1 + SIZE + -i₁₄]))
        && (forall i₁₄: int ::
              (!(  old(i) <= i₁₄
                && i₁₄ < i
              )
                 ==> a[i₁₄] == old(a)[i₁₄]
                  && b[i₁₄] == old(b)[i₁₄]));
    {
      a[i] := a_copy[SIZE - i - 1];
      b[i] := b_copy[SIZE - i - 1];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₁₉: int ::
              (  old(i) <= i₁₉
                && i₁₉ < i
                 ==> i₁₉ < SIZE
                  && a[i₁₉] == old(b)[i₁₉]
                  && b[i₁₉] == old(a)[i₁₉]))
        && (forall i₁₉: int ::
              (!(  old(i) <= i₁₉
                && i₁₉ < i
              )
                 ==> a[i₁₉] == old(a)[i₁₉]
                  && b[i₁₉] == old(b)[i₁₉]));
    {
      tmp := a[i];
      a[i] := b[i];
      b[i] := tmp;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₂₅: int ::
              (  old(i) <= i₂₅
                && i₂₅ < i
                 ==> i₂₅ < SIZE
                  && a[i₂₅] == old(b)[i₂₅]
                  && b[i₂₅] == old(a)[i₂₅]))
        && (forall i₂₅: int ::
              (!(  old(i) <= i₂₅
                && i₂₅ < i
              )
                 ==> a[i₂₅] == old(a)[i₂₅]
                  && b[i₂₅] == old(b)[i₂₅]));
    {
      tmp := a[i];
      a[i] := b[i];
      b[i] := tmp;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₃₀: int ::
              (  old(i) <= i₃₀
                && i₃₀ < i
                 ==> i₃₀ < SIZE));
    {
      assert a[i] == a_copy[SIZE - i - 1];
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

