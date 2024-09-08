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
    invariant old(i) <= i
      && i <= 100000
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> (exists __VERIFIER_nondet_int₁₃: int ::
                      i₄ < 100000
                      && a[i₄] == __VERIFIER_nondet_int₁₃)))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> a[i₄] == old(a)[i₄]));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> 0 <= a[i₇]
                  && i₇ < 100000
                  && b[i₇] == 1
                ||   !(0 <= a[i₇]
                  )
                  && i₇ < 100000
                  && b[i₇] == 0))
      && (forall i₇: int ::
            (!(  old(i) <= i₇
              && i₇ < i
            )
               ==> b[i₇] == old(b)[i₇]));
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
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> a[i₁₁] < 0
                  && b[i₁₁] != 0
                  && 0 <= a[i₁₁]
                  && b[i₁₁] == 0
                  && i₁₁ < 100000
                ||   a[i₁₁] < 0
                  && b[i₁₁] != 0
                  && !(  0 <= a[i₁₁]
                    && b[i₁₁] == 0
                  )
                  && i₁₁ < 100000
                ||   !(  a[i₁₁] < 0
                    && b[i₁₁] != 0
                  )
                  && 0 <= a[i₁₁]
                  && b[i₁₁] == 0
                  && i₁₁ < 100000
                ||   !(  a[i₁₁] < 0
                    && b[i₁₁] != 0
                  )
                  && !(  0 <= a[i₁₁]
                    && b[i₁₁] == 0
                  )
                  && i₁₁ < 100000));
  {
    if(0 <= a[i] && !(b[i] != 0)) {
      f := 0;
    }
    if(a[i] < 0 && b[i] != 0) {
      f := 0;
    }
    i := i + 1;
  }
  assert f != 0;
  c#result := 0;
  return;
}

