data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure _strcmp(src: [int]int, dst: [int]int)
  returns (c#result: int)
{
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> dst[i₂] == src[i₂]
                && i₂ < 100000))
      && (forall i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> !(  dst[i₂] != src[i₂]
                && i₂ < 100000
              )));
  {
    if(dst[i] != src[i]) {
      c#result := 1;
      return;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var i: int := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> (exists nondet_int₁₇: int, nondet_int₂₈: int ::
                      -2147483648 <= nondet_int₂₈
                      && nondet_int₂₈ < 2147483648
                      && -2147483648 <= nondet_int₁₇
                      && nondet_int₁₇ < 2147483648
                      && i₉ < 100000
                      && a[i₉] == nondet_int₁₇
                      && b[i₉] == nondet_int₂₈)))
      && (forall i₉: int ::
            (!(  old(i) <= i₉
              && i₉ < i
            )
               ==> a[i₉] == old(a)[i₉]
                && b[i₉] == old(b)[i₉]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[i] := nondet_int₁;
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    b[i] := nondet_int₂;
    i := i + 1;
  }
  var _strcmp₄: int;
  _strcmp₄ := call _strcmp(a, b);
  var c: int;
  c := _strcmp₄;
  if(c == 0) {
    var x: int;
    x := 0;
    while(x < 100000)
      decreases 100000 - x;
      invariant old(x) <= x
        && (forall x₁₆: int ::
              (  old(x) <= x₁₆
                && x₁₆ < x
                 ==> x₁₆ < 100000));
    {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

