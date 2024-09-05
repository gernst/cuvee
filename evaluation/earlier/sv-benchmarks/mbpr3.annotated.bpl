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
    var CCCELVOL3: int := 7;
    var CCCELVOL2: int := 3;
    var CCCELVOL1: int := 1;
    if(CELLCOUNT % 3 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 3 == 0;
    i := 1;
    while(i <= CELLCOUNT / 3)
      decreases CELLCOUNT / 3 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 3
        && (forall x₅: int ::
              ((exists i₄: int ::
                    if(x₅ == -1 + 3 * i₄) then old(i) <= i₄ && i₄ < i else if(x₅ == -2 + 3 * i₄) then old(i) <= i₄ && i₄ < i else x₅ == -3 + 3 * i₄ && old(i) <= i₄ && i₄ < i)
                 ==> (exists i₄: int ::
                          MINVAL <= CCCELVOL3
                          && i₄ <= CELLCOUNT / 3
                          && if(x₅ == -1 + 3 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-3 + 3 * i₄ := CCCELVOL3][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-3 + 3 * i₄ := CCCELVOL3][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && old(i) <= i₄ && i₄ < i && volArray[x₅] == CCCELVOL3)
                  || (exists i₄: int ::
                          !(MINVAL <= CCCELVOL3
                          )
                          && i₄ <= CELLCOUNT / 3
                          && if(x₅ == -1 + 3 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-3 + 3 * i₄ := 0][-1 + 3 * i₄] else if(x₅ == -2 + 3 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-3 + 3 * i₄ := 0][-2 + 3 * i₄] else x₅ == -3 + 3 * i₄ && old(i) <= i₄ && i₄ < i && volArray[x₅] == 0)))
        && (forall x₅: int ::
              (!((exists i₄: int ::
                    if(x₅ == -1 + 3 * i₄) then old(i) <= i₄ && i₄ < i else if(x₅ == -2 + 3 * i₄) then old(i) <= i₄ && i₄ < i else x₅ == -3 + 3 * i₄ && old(i) <= i₄ && i₄ < i)
              )
                 ==> volArray[x₅] == old(volArray[x₅])))
        && (forall i₄: int ::
              (  old(i) <= i₄
                && i₄ < i
                 ==> i₄ <= CELLCOUNT / 3));
    {
      if(MINVAL <= CCCELVOL3) {
        volArray := volArray[i * 3 - 3 := CCCELVOL3];
      } else {
        volArray := volArray[i * 3 - 3 := 0];
      }
      volArray := volArray[i * 3 - 2 := volArray[i * 3 - 2]];
      volArray := volArray[i * 3 - 1 := volArray[i * 3 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 3)
      decreases CELLCOUNT / 3 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 3
        && (forall x₉: int ::
              ((exists i₈: int ::
                    if(x₉ == -1 + 3 * i₈) then old(i) <= i₈ && i₈ < i else if(x₉ == -3 + 3 * i₈) then old(i) <= i₈ && i₈ < i else x₉ == -2 + 3 * i₈ && old(i) <= i₈ && i₈ < i)
                 ==> (exists i₈: int ::
                          MINVAL <= CCCELVOL2
                          && i₈ <= CELLCOUNT / 3
                          && if(x₉ == -1 + 3 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-2 + 3 * i₈ := CCCELVOL2][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-2 + 3 * i₈ := CCCELVOL2][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && old(i) <= i₈ && i₈ < i && volArray[x₉] == CCCELVOL2)
                  || (exists i₈: int ::
                          !(MINVAL <= CCCELVOL2
                          )
                          && i₈ <= CELLCOUNT / 3
                          && if(x₉ == -1 + 3 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-2 + 3 * i₈ := 0][-1 + 3 * i₈] else if(x₉ == -3 + 3 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-2 + 3 * i₈ := 0][-3 + 3 * i₈] else x₉ == -2 + 3 * i₈ && old(i) <= i₈ && i₈ < i && volArray[x₉] == 0)))
        && (forall x₉: int ::
              (!((exists i₈: int ::
                    if(x₉ == -1 + 3 * i₈) then old(i) <= i₈ && i₈ < i else if(x₉ == -3 + 3 * i₈) then old(i) <= i₈ && i₈ < i else x₉ == -2 + 3 * i₈ && old(i) <= i₈ && i₈ < i)
              )
                 ==> volArray[x₉] == old(volArray[x₉])))
        && (forall i₈: int ::
              (  old(i) <= i₈
                && i₈ < i
                 ==> i₈ <= CELLCOUNT / 3));
    {
      if(MINVAL <= CCCELVOL2) {
        volArray := volArray[i * 3 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 3 - 2 := 0];
      }
      volArray := volArray[i * 3 - 3 := volArray[i * 3 - 3]];
      volArray := volArray[i * 3 - 1 := volArray[i * 3 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 3)
      decreases CELLCOUNT / 3 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 3
        && (forall x₁₃: int ::
              ((exists i₁₂: int ::
                    if(x₁₃ == -3 + 3 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else if(x₁₃ == -2 + 3 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else x₁₃ == -1 + 3 * i₁₂ && old(i) <= i₁₂ && i₁₂ < i)
                 ==> (exists i₁₂: int ::
                          MINVAL <= CCCELVOL1
                          && i₁₂ <= CELLCOUNT / 3
                          && if(x₁₃ == -3 + 3 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-1 + 3 * i₁₂ := CCCELVOL1][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-1 + 3 * i₁₂ := CCCELVOL1][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == CCCELVOL1)
                  || (exists i₁₂: int ::
                          !(MINVAL <= CCCELVOL1
                          )
                          && i₁₂ <= CELLCOUNT / 3
                          && if(x₁₃ == -3 + 3 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-1 + 3 * i₁₂ := 0][-3 + 3 * i₁₂] else if(x₁₃ == -2 + 3 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-1 + 3 * i₁₂ := 0][-2 + 3 * i₁₂] else x₁₃ == -1 + 3 * i₁₂ && old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == 0)))
        && (forall x₁₃: int ::
              (!((exists i₁₂: int ::
                    if(x₁₃ == -3 + 3 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else if(x₁₃ == -2 + 3 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else x₁₃ == -1 + 3 * i₁₂ && old(i) <= i₁₂ && i₁₂ < i)
              )
                 ==> volArray[x₁₃] == old(volArray[x₁₃])))
        && (forall i₁₂: int ::
              (  old(i) <= i₁₂
                && i₁₂ < i
                 ==> i₁₂ <= CELLCOUNT / 3));
    {
      if(MINVAL <= CCCELVOL1) {
        volArray := volArray[i * 3 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 3 - 1 := 0];
      }
      volArray := volArray[i * 3 - 2 := volArray[i * 3 - 2]];
      volArray := volArray[i * 3 - 3 := volArray[i * 3 - 3]];
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT)
      decreases CELLCOUNT - i;
      invariant true
        && old(i) <= i
        && i <= CELLCOUNT
        && (forall i₁₆: int ::
              (  old(i) <= i₁₆
                && i₁₆ < i
                 ==> i₁₆ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

