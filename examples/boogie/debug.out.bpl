procedure main()
{
  var i: int;
  var N: int;
  var a: [int]int;
  i := 0;
  while(i <= N)
    decreases N + 1 - i;
    invariant 0 <= i
      && i <= 1 + N
      && (forall x₅: int ::
            ((exists i₄: int ::
                  if(x₅ == 1 + 2 * i₄) then i₄ <= N && 0 <= i₄ && i₄ < i else x₅ == 2 * i₄ && i₄ <= N && 0 <= i₄ && i₄ < i)
               ==> (exists i₄: int ::
                    if(x₅ == 1 + 2 * i₄) then i₄ <= N && 0 <= i₄ && i₄ < i && a[x₅] == 17 else x₅ == 2 * i₄ && i₄ <= N && 0 <= i₄ && i₄ < i && a[x₅] == 7)))
      && (forall x₅: int ::
            (!((exists i₄: int ::)
                  if(x₅ == 1 + 2 * i₄) then i₄ <= N && 0 <= i₄ && i₄ < i else x₅ == 2 * i₄ && i₄ <= N && 0 <= i₄ && i₄ < i)
               ==> a[x₅] == old(a[x₅])))
      && (forall i₄: int ::
            (  0 <= i₄
              && i₄ < i
               ==> i₄ <= N));
  {
    a := a[2 * i := 7];
    a := a[2 * i + 1 := 17];
    i := i + 1;
  }
}

