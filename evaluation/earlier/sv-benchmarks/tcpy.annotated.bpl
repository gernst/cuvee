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
    var a: [int]int;
    var acopy: [int]int;
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₆: int ::
              (  old(i) <= i₆
                && i₆ < i
                 ==> (exists nondet_int₁₅: int ::
                        -2147483648 <= nondet_int₁₅
                        && nondet_int₁₅ < 2147483648
                        && i₆ < SIZE
                        && a[i₆] == nondet_int₁₅)))
        && (forall i₆: int ::
              (!(  old(i) <= i₆
                && i₆ < i
              )
                 ==> a[i₆] == old(a)[i₆]));
    {
      var nondet_int₁: int;
      assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
      a[i] := nondet_int₁;
      i := i + 1;
    }
    if(SIZE % 2 != 0) {
      c#result := 1;
      return;
    }
    assume SIZE % 2 == 0;
    i := 0;
    while(i < SIZE / 2)
      decreases SIZE / 2 - i;
      invariant old(i) <= i
        && (forall i₉: int ::
              (  old(i) <= i₉
                && i₉ < i
                 ==> i₉ < SIZE / 2
                  && acopy[i₉] == a[i₉]
                  && (-1 + SIZE + -i₉ != i₉
                     ==> acopy[-1 + SIZE + -i₉] == a[-1 + SIZE + -i₉])))
        && (forall i₉: int ::
              (!(  old(i) <= i₉
                && i₉ < i
              )
                 ==> acopy[i₉] == old(acopy)[i₉]
                  && acopy[-1 + SIZE + -i₉] == old(acopy)[-1 + SIZE + -i₉]));
    {
      acopy[((SIZE - i) - 1)] := a[SIZE - i - 1];
      acopy[i] := a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant old(i) <= i
        && (forall i₁₂: int ::
              (  old(i) <= i₁₂
                && i₁₂ < i
                 ==> i₁₂ < SIZE));
    {
      assert acopy[i] == a[i];
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

