procedure main()
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
      && 1 <= i
      && i <= N
      && (forall x₉: int ::
            ((exists i₈: int ::
                    x₉ == i₈
                    && 1 <= i₈
                    && i₈ < i)
               ==> (exists j₆: int, k₇: int, i₈: int ::
                      k₇ + j₆ == 0
                      && 10000 < k₇
                      && 10000 < j₆
                      && i₈ < N
                      && x₉ == i₈
                      && 1 <= i₈
                      && i₈ < i
                      && a[x₉] == j₆)))
      && (forall x₉: int ::
            (!((exists i₈: int ::
                    x₉ == i₈
                    && 1 <= i₈
                    && i₈ < i)
            )
               ==> a[x₉] == old(a[x₉])))
      && (forall x₁₀: int ::
            ((exists i₈: int ::
                    x₁₀ == i₈
                    && 1 <= i₈
                    && i₈ < i)
               ==> (exists j₆: int, k₇: int, i₈: int ::
                      k₇ + j₆ == 0
                      && 10000 < k₇
                      && 10000 < j₆
                      && i₈ < N
                      && x₁₀ == i₈
                      && 1 <= i₈
                      && i₈ < i
                      && b[x₁₀] == -k₇)))
      && (forall x₁₀: int ::
            (!((exists i₈: int ::
                    x₁₀ == i₈
                    && 1 <= i₈
                    && i₈ < i)
            )
               ==> b[x₁₀] == old(b[x₁₀])))
      && (forall i₈: int ::
            (  1 <= i₈
              && i₈ < i
               ==> i₈ < N));
  {
    var j: int;
    var k: int;
    assume 10000 < j && 10000 < j;
    assume 10000 < k && 10000 < k;
    assume j + k == 0;
    a := a[i := j];
    b := b[i := -k];
    i := i + 1;
  }
  assert forall x: int :: 1 <= x && x < N ==> a[x] + b[x] == 0;
}

