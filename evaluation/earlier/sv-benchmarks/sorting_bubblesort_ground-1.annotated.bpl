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
  var a: [int]int;
  var j: int := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant old(j) <= j
      && (forall j₃: int ::
            (  old(j) <= j₃
              && j₃ < j
               ==> (exists nondet_int₁₂: int ::
                      -2147483648 <= nondet_int₁₂
                      && nondet_int₁₂ < 2147483648
                      && j₃ < 100000
                      && a[j₃] == nondet_int₁₂)))
      && (forall j₃: int ::
            (!(  old(j) <= j₃
              && j₃ < j
            )
               ==> a[j₃] == old(a)[j₃]));
  {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[j] := nondet_int₁;
    j := j + 1;
  }
  var swapped: int := 1;
  while(swapped != 0)
    invariant (forall swapped₁₁: int ::
          (exists a₈: [int]int, i₁₀: int ::
                  1 <= i₁₀
                  && (forall i₇: int ::
                        (  1 <= i₇
                          && i₇ < i₁₀
                           ==> a₈[i₇] < a₈[-1 + i₇]
                              && i₇ < 100000
                              && a₈[-1 + i₇] == a[i₇]
                              && (i₇ != -1 + i₇
                                 ==> a₈[i₇] == a[-1 + i₇])
                            ||   !(a₈[i₇] < a₈[-1 + i₇]
                              )
                              && i₇ < 100000))
                  && (forall i₇: int ::
                        (!(  1 <= i₇
                          && i₇ < i₁₀
                        )
                           ==> a₈[-1 + i₇] == a[-1 + i₇]
                            && a₈[i₇] == a[i₇]))
                  && !(i₁₀ < 100000
                  )
                  && swapped₁₁ != 0));
  {
    swapped := 0;
    var i: int := 1;
    while(i < 100000)
      decreases 100000 - i;
      invariant old(i) <= i
        && (forall i₇: int ::
              (  old(i) <= i₇
                && i₇ < i
                 ==> a[i₇] < a[-1 + i₇]
                    && i₇ < 100000
                    && a[-1 + i₇] == old(a)[i₇]
                    && (i₇ != -1 + i₇
                       ==> a[i₇] == old(a)[-1 + i₇])
                  ||   !(a[i₇] < a[-1 + i₇]
                    )
                    && i₇ < 100000))
        && (forall i₇: int ::
              (!(  old(i) <= i₇
                && i₇ < i
              )
                 ==> a[-1 + i₇] == old(a)[-1 + i₇]
                  && a[i₇] == old(a)[i₇]));
    {
      if(a[i] < a[i - 1]) {
        var t: int := a[i];
        a[i] := a[i - 1];
        a[(i - 1)] := t;
        swapped := 1;
      }
      i := i + 1;
    }
  }
  var x: int;
  var y: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₁₉: int ::
            (  old(x) <= x₁₉
              && x₁₉ < x
               ==> (exists y₁₇: int ::
                      1 + x₁₉ <= y₁₇
                      && (forall y₁₆: int ::
                            (  1 + x₁₉ <= y₁₆
                              && y₁₆ < y₁₇
                               ==> y₁₆ < 100000))
                      && !(y₁₇ < 100000
                      )
                      && x₁₉ < 100000)));
  {
    y := x + 1;
    while(y < 100000)
      decreases 100000 - y;
      invariant old(y) <= y
        && (forall y₁₆: int ::
              (  old(y) <= y₁₆
                && y₁₆ < y
                 ==> y₁₆ < 100000));
    {
      assert a[x] <= a[y];
      y := y + 1;
    }
    x := x + 1;
  }
  c#result := 0;
  return;
}

