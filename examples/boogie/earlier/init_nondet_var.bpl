procedure main()
{
  var a: [int]int, b: [int]int;
  var N: int;
  assume 0 <= N;
  var i: int := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
               ==> (exists z₄: int, i₅: int ::
                      i₅ < N
                      && x₆ == i₅
                      && 0 <= i₅
                      && i₅ < i
                      && a[x₆] == z₄)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall x₇: int ::
            ((exists i₅: int ::
                    x₇ == i₅
                    && 0 <= i₅
                    && i₅ < i)
               ==> (exists z₄: int, i₅: int ::
                      i₅ < N
                      && x₇ == i₅
                      && 0 <= i₅
                      && i₅ < i
                      && b[x₇] == z₄)))
      && (forall x₇: int ::
            (!((exists i₅: int ::
                    x₇ == i₅
                    && 0 <= i₅
                    && i₅ < i)
            )
               ==> b[x₇] == old(b[x₇])))
      && (forall i₅: int ::
            (  0 <= i₅
              && i₅ < i
               ==> i₅ < N));
  {
    var z: int;
    a := a[i := z];
    b := b[i := z];
    i := i + 1;
  }
  assert forall k: int :: 0 <= k && k < N ==> a[k] == b[k];
}

