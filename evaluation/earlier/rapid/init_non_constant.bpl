procedure init_non_constant(alength: int, v: int)
  returns (a: [int]int)
  requires 0 <= alength
    && true
    && true
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
             ==> a[pos] == 2 * pos + v))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
            && 0 <= v
             ==> 2 * pos <= a[pos]))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
            && 0 < v
             ==> 2 * pos < a[pos]))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
            && v == 80
             ==> 2 * pos < a[pos]));
{
  var i: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant 0 <= i
      && old(i) <= i
      && i <= alength
      && (forall x₂: int ::
            ((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int ::
                      i₁ < alength
                      && 0 <= i₁
                      && x₂ == i₁
                      && old(i) <= i₁
                      && i₁ < i
                      && a[x₂] == v + 2 * i₁)))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> a[x₂] == old(a[x₂])))
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i₁) <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < alength));
  {
    a := a[i := 2 * i + v];
    i := i + 1;
  }
}

