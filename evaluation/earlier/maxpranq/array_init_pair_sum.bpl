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
  var N: int;
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  assume 0 < N;
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₂: int ::
            ((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
               ==> (exists j₉: int, k₁₀: int, i₁₁: int ::
                      3 <= j₉ + k₁₀
                      && i₁₁ < N
                      && x₁₂ == i₁₁
                      && old(i) <= i₁₁
                      && i₁₁ < i
                      && a[x₁₂] == j₉)))
      && (forall x₁₂: int ::
            (!((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
            )
               ==> a[x₁₂] == old(a[x₁₂])))
      && (forall x₁₃: int ::
            ((exists i₁₁: int ::
                    x₁₃ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
               ==> (exists j₉: int, k₁₀: int, i₁₁: int ::
                      3 <= j₉ + k₁₀
                      && i₁₁ < N
                      && x₁₃ == i₁₁
                      && old(i) <= i₁₁
                      && i₁₁ < i
                      && b[x₁₃] == k₁₀)))
      && (forall x₁₃: int ::
            (!((exists i₁₁: int ::
                    x₁₃ == i₁₁
                    && old(i) <= i₁₁
                    && i₁₁ < i)
            )
               ==> b[x₁₃] == old(b[x₁₃])))
      && (forall i₁₁: int ::
            (  old(i₁₁) <= i₁₁
              && old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < N));
  {
    var j: int;
    var k: int;
    assume 3 <= j + k;
    a := a[i := j];
    b := b[i := k];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₈: int ::
            ((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
               ==> (exists i₁₇: int ::
                      i₁₇ < N
                      && x₁₈ == i₁₇
                      && old(i) <= i₁₇
                      && i₁₇ < i
                      && c[x₁₈] == a[i₁₇] + b[i₁₇])))
      && (forall x₁₈: int ::
            (!((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
            )
               ==> c[x₁₈] == old(c[x₁₈])))
      && (forall i₁₇: int ::
            (  old(i₁₇) <= i₁₇
              && old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < N));
  {
    c := c[i := a[i] + b[i]];
    i := i + 1;
  }
  i := 1;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₂₁: int ::
            (  old(i₂₁) <= i₂₁
              && old(i) <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < N));
  {
    assert 3 <= c[i];
    i := i + 1;
  }
}

