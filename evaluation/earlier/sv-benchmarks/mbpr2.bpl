data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var CELLCOUNT: int;

procedure main()
  returns (c#result: int)
  modifies CELLCOUNT;
{
  havoc CELLCOUNT;
  if(1 < CELLCOUNT) {
    var MINVAL: int := 2;
    var i: int;
    var volArray: [int]int;
    var CCCELVOL2: int := 3;
    var CCCELVOL1: int := 1;
    if(CELLCOUNT % 2 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 2 == 0;
    i := 1;
    while(i <= CELLCOUNT / 2)
      decreases CELLCOUNT / 2 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 2
        && (forall x₅: int ::
              ((exists i₄: int ::
                    if(x₅ == -1 + 2 * i₄) then old(i) <= i₄ && i₄ < i else x₅ == -2 + 2 * i₄ && old(i) <= i₄ && i₄ < i)
                 ==> (exists i₄: int ::
                          MINVAL <= CCCELVOL2
                          && i₄ <= CELLCOUNT / 2
                          && if(x₅ == -1 + 2 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-2 + 2 * i₄ := CCCELVOL2][-1 + 2 * i₄] else x₅ == -2 + 2 * i₄ && old(i) <= i₄ && i₄ < i && volArray[x₅] == CCCELVOL2)
                  || (exists i₄: int ::
                          !(MINVAL <= CCCELVOL2
                          )
                          && i₄ <= CELLCOUNT / 2
                          && if(x₅ == -1 + 2 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-2 + 2 * i₄ := 0][-1 + 2 * i₄] else x₅ == -2 + 2 * i₄ && old(i) <= i₄ && i₄ < i && volArray[x₅] == 0)))
        && (forall x₅: int ::
              (!((exists i₄: int ::
                    if(x₅ == -1 + 2 * i₄) then old(i) <= i₄ && i₄ < i else x₅ == -2 + 2 * i₄ && old(i) <= i₄ && i₄ < i)
              )
                 ==> volArray[x₅] == old(volArray[x₅])))
        && (forall i₄: int ::
              (  old(i₄) <= i₄
                && old(i) <= i₄
                && i₄ < i
                 ==> i₄ <= CELLCOUNT / 2));
    {
      if(MINVAL <= CCCELVOL2) {
        volArray := volArray[i * 2 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 2 - 2 := 0];
      }
      volArray := volArray[i * 2 - 1 := volArray[i * 2 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 2)
      decreases CELLCOUNT / 2 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 2
        && (forall x₉: int ::
              ((exists i₈: int ::
                    if(x₉ == -2 + 2 * i₈) then old(i) <= i₈ && i₈ < i else x₉ == -1 + 2 * i₈ && old(i) <= i₈ && i₈ < i)
                 ==> (exists i₈: int ::
                          MINVAL <= CCCELVOL1
                          && i₈ <= CELLCOUNT / 2
                          && if(x₉ == -2 + 2 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-1 + 2 * i₈ := CCCELVOL1][-2 + 2 * i₈] else x₉ == -1 + 2 * i₈ && old(i) <= i₈ && i₈ < i && volArray[x₉] == CCCELVOL1)
                  || (exists i₈: int ::
                          !(MINVAL <= CCCELVOL1
                          )
                          && i₈ <= CELLCOUNT / 2
                          && if(x₉ == -2 + 2 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-1 + 2 * i₈ := 0][-2 + 2 * i₈] else x₉ == -1 + 2 * i₈ && old(i) <= i₈ && i₈ < i && volArray[x₉] == 0)))
        && (forall x₉: int ::
              (!((exists i₈: int ::
                    if(x₉ == -2 + 2 * i₈) then old(i) <= i₈ && i₈ < i else x₉ == -1 + 2 * i₈ && old(i) <= i₈ && i₈ < i)
              )
                 ==> volArray[x₉] == old(volArray[x₉])))
        && (forall i₈: int ::
              (  old(i₈) <= i₈
                && old(i) <= i₈
                && i₈ < i
                 ==> i₈ <= CELLCOUNT / 2));
    {
      if(MINVAL <= CCCELVOL1) {
        volArray := volArray[i * 2 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 2 - 1 := 0];
      }
      volArray := volArray[i * 2 - 2 := volArray[i * 2 - 2]];
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT)
      decreases CELLCOUNT - i;
      invariant true
        && old(i) <= i
        && i <= CELLCOUNT
        && (forall i₁₂: int ::
              (  old(i₁₂) <= i₁₂
                && old(i) <= i₁₂
                && i₁₂ < i
                 ==> i₁₂ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

