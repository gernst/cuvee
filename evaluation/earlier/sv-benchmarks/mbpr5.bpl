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
    var CCCELVOL5: int := 8;
    var CCCELVOL4: int := 5;
    var CCCELVOL3: int := 7;
    var CCCELVOL2: int := 3;
    var CCCELVOL1: int := 1;
    if(CELLCOUNT % 5 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 5 == 0;
    i := 1;
    while(i <= CELLCOUNT / 5)
      decreases CELLCOUNT / 5 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 5
        && (forall x₅: int ::
              ((exists i₄: int ::
                    if(x₅ == -1 + 5 * i₄) then old(i) <= i₄ && i₄ < i else if(x₅ == -2 + 5 * i₄) then old(i) <= i₄ && i₄ < i else if(x₅ == -3 + 5 * i₄) then old(i) <= i₄ && i₄ < i else if(x₅ == -4 + 5 * i₄) then old(i) <= i₄ && i₄ < i else x₅ == -5 + 5 * i₄ && old(i) <= i₄ && i₄ < i)
                 ==> (exists i₄: int ::
                          MINVAL <= CCCELVOL5
                          && i₄ <= CELLCOUNT / 5
                          && if(x₅ == -1 + 5 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-5 + 5 * i₄ := CCCELVOL5][-1 + 5 * i₄] else if(x₅ == -2 + 5 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-5 + 5 * i₄ := CCCELVOL5][-2 + 5 * i₄] else if(x₅ == -3 + 5 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-5 + 5 * i₄ := CCCELVOL5][-3 + 5 * i₄] else if(x₅ == -4 + 5 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-5 + 5 * i₄ := CCCELVOL5][-4 + 5 * i₄] else x₅ == -5 + 5 * i₄ && old(i) <= i₄ && i₄ < i && volArray[x₅] == CCCELVOL5)
                  || (exists i₄: int ::
                          !(MINVAL <= CCCELVOL5
                          )
                          && i₄ <= CELLCOUNT / 5
                          && if(x₅ == -1 + 5 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-5 + 5 * i₄ := 0][-1 + 5 * i₄] else if(x₅ == -2 + 5 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-5 + 5 * i₄ := 0][-2 + 5 * i₄] else if(x₅ == -3 + 5 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-5 + 5 * i₄ := 0][-3 + 5 * i₄] else if(x₅ == -4 + 5 * i₄) then old(i) <= i₄ && i₄ < i && volArray[x₅] == volArray[-5 + 5 * i₄ := 0][-4 + 5 * i₄] else x₅ == -5 + 5 * i₄ && old(i) <= i₄ && i₄ < i && volArray[x₅] == 0)))
        && (forall x₅: int ::
              (!((exists i₄: int ::
                    if(x₅ == -1 + 5 * i₄) then old(i) <= i₄ && i₄ < i else if(x₅ == -2 + 5 * i₄) then old(i) <= i₄ && i₄ < i else if(x₅ == -3 + 5 * i₄) then old(i) <= i₄ && i₄ < i else if(x₅ == -4 + 5 * i₄) then old(i) <= i₄ && i₄ < i else x₅ == -5 + 5 * i₄ && old(i) <= i₄ && i₄ < i)
              )
                 ==> volArray[x₅] == old(volArray[x₅])))
        && (forall i₄: int ::
              (  old(i₄) <= i₄
                && old(i) <= i₄
                && i₄ < i
                 ==> i₄ <= CELLCOUNT / 5));
    {
      if(MINVAL <= CCCELVOL5) {
        volArray := volArray[i * 5 - 5 := CCCELVOL5];
      } else {
        volArray := volArray[i * 5 - 5 := 0];
      }
      volArray := volArray[i * 5 - 4 := volArray[i * 5 - 4]];
      volArray := volArray[i * 5 - 3 := volArray[i * 5 - 3]];
      volArray := volArray[i * 5 - 2 := volArray[i * 5 - 2]];
      volArray := volArray[i * 5 - 1 := volArray[i * 5 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 5)
      decreases CELLCOUNT / 5 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 5
        && (forall x₉: int ::
              ((exists i₈: int ::
                    if(x₉ == -1 + 5 * i₈) then old(i) <= i₈ && i₈ < i else if(x₉ == -2 + 5 * i₈) then old(i) <= i₈ && i₈ < i else if(x₉ == -3 + 5 * i₈) then old(i) <= i₈ && i₈ < i else if(x₉ == -5 + 5 * i₈) then old(i) <= i₈ && i₈ < i else x₉ == -4 + 5 * i₈ && old(i) <= i₈ && i₈ < i)
                 ==> (exists i₈: int ::
                          MINVAL <= CCCELVOL4
                          && i₈ <= CELLCOUNT / 5
                          && if(x₉ == -1 + 5 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-4 + 5 * i₈ := CCCELVOL4][-1 + 5 * i₈] else if(x₉ == -2 + 5 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-4 + 5 * i₈ := CCCELVOL4][-2 + 5 * i₈] else if(x₉ == -3 + 5 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-4 + 5 * i₈ := CCCELVOL4][-3 + 5 * i₈] else if(x₉ == -5 + 5 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-4 + 5 * i₈ := CCCELVOL4][-5 + 5 * i₈] else x₉ == -4 + 5 * i₈ && old(i) <= i₈ && i₈ < i && volArray[x₉] == CCCELVOL4)
                  || (exists i₈: int ::
                          !(MINVAL <= CCCELVOL4
                          )
                          && i₈ <= CELLCOUNT / 5
                          && if(x₉ == -1 + 5 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-4 + 5 * i₈ := 0][-1 + 5 * i₈] else if(x₉ == -2 + 5 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-4 + 5 * i₈ := 0][-2 + 5 * i₈] else if(x₉ == -3 + 5 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-4 + 5 * i₈ := 0][-3 + 5 * i₈] else if(x₉ == -5 + 5 * i₈) then old(i) <= i₈ && i₈ < i && volArray[x₉] == volArray[-4 + 5 * i₈ := 0][-5 + 5 * i₈] else x₉ == -4 + 5 * i₈ && old(i) <= i₈ && i₈ < i && volArray[x₉] == 0)))
        && (forall x₉: int ::
              (!((exists i₈: int ::
                    if(x₉ == -1 + 5 * i₈) then old(i) <= i₈ && i₈ < i else if(x₉ == -2 + 5 * i₈) then old(i) <= i₈ && i₈ < i else if(x₉ == -3 + 5 * i₈) then old(i) <= i₈ && i₈ < i else if(x₉ == -5 + 5 * i₈) then old(i) <= i₈ && i₈ < i else x₉ == -4 + 5 * i₈ && old(i) <= i₈ && i₈ < i)
              )
                 ==> volArray[x₉] == old(volArray[x₉])))
        && (forall i₈: int ::
              (  old(i₈) <= i₈
                && old(i) <= i₈
                && i₈ < i
                 ==> i₈ <= CELLCOUNT / 5));
    {
      if(MINVAL <= CCCELVOL4) {
        volArray := volArray[i * 5 - 4 := CCCELVOL4];
      } else {
        volArray := volArray[i * 5 - 4 := 0];
      }
      volArray := volArray[i * 5 - 5 := volArray[i * 5 - 5]];
      volArray := volArray[i * 5 - 3 := volArray[i * 5 - 3]];
      volArray := volArray[i * 5 - 2 := volArray[i * 5 - 2]];
      volArray := volArray[i * 5 - 1 := volArray[i * 5 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 5)
      decreases CELLCOUNT / 5 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 5
        && (forall x₁₃: int ::
              ((exists i₁₂: int ::
                    if(x₁₃ == -1 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else if(x₁₃ == -2 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else if(x₁₃ == -4 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else if(x₁₃ == -5 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else x₁₃ == -3 + 5 * i₁₂ && old(i) <= i₁₂ && i₁₂ < i)
                 ==> (exists i₁₂: int ::
                          MINVAL <= CCCELVOL3
                          && i₁₂ <= CELLCOUNT / 5
                          && if(x₁₃ == -1 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-3 + 5 * i₁₂ := CCCELVOL3][-1 + 5 * i₁₂] else if(x₁₃ == -2 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-3 + 5 * i₁₂ := CCCELVOL3][-2 + 5 * i₁₂] else if(x₁₃ == -4 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-3 + 5 * i₁₂ := CCCELVOL3][-4 + 5 * i₁₂] else if(x₁₃ == -5 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-3 + 5 * i₁₂ := CCCELVOL3][-5 + 5 * i₁₂] else x₁₃ == -3 + 5 * i₁₂ && old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == CCCELVOL3)
                  || (exists i₁₂: int ::
                          !(MINVAL <= CCCELVOL3
                          )
                          && i₁₂ <= CELLCOUNT / 5
                          && if(x₁₃ == -1 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-3 + 5 * i₁₂ := 0][-1 + 5 * i₁₂] else if(x₁₃ == -2 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-3 + 5 * i₁₂ := 0][-2 + 5 * i₁₂] else if(x₁₃ == -4 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-3 + 5 * i₁₂ := 0][-4 + 5 * i₁₂] else if(x₁₃ == -5 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == volArray[-3 + 5 * i₁₂ := 0][-5 + 5 * i₁₂] else x₁₃ == -3 + 5 * i₁₂ && old(i) <= i₁₂ && i₁₂ < i && volArray[x₁₃] == 0)))
        && (forall x₁₃: int ::
              (!((exists i₁₂: int ::
                    if(x₁₃ == -1 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else if(x₁₃ == -2 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else if(x₁₃ == -4 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else if(x₁₃ == -5 + 5 * i₁₂) then old(i) <= i₁₂ && i₁₂ < i else x₁₃ == -3 + 5 * i₁₂ && old(i) <= i₁₂ && i₁₂ < i)
              )
                 ==> volArray[x₁₃] == old(volArray[x₁₃])))
        && (forall i₁₂: int ::
              (  old(i₁₂) <= i₁₂
                && old(i) <= i₁₂
                && i₁₂ < i
                 ==> i₁₂ <= CELLCOUNT / 5));
    {
      if(MINVAL <= CCCELVOL3) {
        volArray := volArray[i * 5 - 3 := CCCELVOL3];
      } else {
        volArray := volArray[i * 5 - 3 := 0];
      }
      volArray := volArray[i * 5 - 5 := volArray[i * 5 - 5]];
      volArray := volArray[i * 5 - 4 := volArray[i * 5 - 4]];
      volArray := volArray[i * 5 - 2 := volArray[i * 5 - 2]];
      volArray := volArray[i * 5 - 1 := volArray[i * 5 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 5)
      decreases CELLCOUNT / 5 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 5
        && (forall x₁₇: int ::
              ((exists i₁₆: int ::
                    if(x₁₇ == -1 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i else if(x₁₇ == -3 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i else if(x₁₇ == -4 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i else if(x₁₇ == -5 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i else x₁₇ == -2 + 5 * i₁₆ && old(i) <= i₁₆ && i₁₆ < i)
                 ==> (exists i₁₆: int ::
                          MINVAL <= CCCELVOL2
                          && i₁₆ <= CELLCOUNT / 5
                          && if(x₁₇ == -1 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-2 + 5 * i₁₆ := CCCELVOL2][-1 + 5 * i₁₆] else if(x₁₇ == -3 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-2 + 5 * i₁₆ := CCCELVOL2][-3 + 5 * i₁₆] else if(x₁₇ == -4 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-2 + 5 * i₁₆ := CCCELVOL2][-4 + 5 * i₁₆] else if(x₁₇ == -5 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-2 + 5 * i₁₆ := CCCELVOL2][-5 + 5 * i₁₆] else x₁₇ == -2 + 5 * i₁₆ && old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == CCCELVOL2)
                  || (exists i₁₆: int ::
                          !(MINVAL <= CCCELVOL2
                          )
                          && i₁₆ <= CELLCOUNT / 5
                          && if(x₁₇ == -1 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-2 + 5 * i₁₆ := 0][-1 + 5 * i₁₆] else if(x₁₇ == -3 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-2 + 5 * i₁₆ := 0][-3 + 5 * i₁₆] else if(x₁₇ == -4 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-2 + 5 * i₁₆ := 0][-4 + 5 * i₁₆] else if(x₁₇ == -5 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == volArray[-2 + 5 * i₁₆ := 0][-5 + 5 * i₁₆] else x₁₇ == -2 + 5 * i₁₆ && old(i) <= i₁₆ && i₁₆ < i && volArray[x₁₇] == 0)))
        && (forall x₁₇: int ::
              (!((exists i₁₆: int ::
                    if(x₁₇ == -1 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i else if(x₁₇ == -3 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i else if(x₁₇ == -4 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i else if(x₁₇ == -5 + 5 * i₁₆) then old(i) <= i₁₆ && i₁₆ < i else x₁₇ == -2 + 5 * i₁₆ && old(i) <= i₁₆ && i₁₆ < i)
              )
                 ==> volArray[x₁₇] == old(volArray[x₁₇])))
        && (forall i₁₆: int ::
              (  old(i₁₆) <= i₁₆
                && old(i) <= i₁₆
                && i₁₆ < i
                 ==> i₁₆ <= CELLCOUNT / 5));
    {
      if(MINVAL <= CCCELVOL2) {
        volArray := volArray[i * 5 - 2 := CCCELVOL2];
      } else {
        volArray := volArray[i * 5 - 2 := 0];
      }
      volArray := volArray[i * 5 - 5 := volArray[i * 5 - 5]];
      volArray := volArray[i * 5 - 4 := volArray[i * 5 - 4]];
      volArray := volArray[i * 5 - 3 := volArray[i * 5 - 3]];
      volArray := volArray[i * 5 - 1 := volArray[i * 5 - 1]];
      i := i + 1;
    }
    i := 1;
    while(i <= CELLCOUNT / 5)
      decreases CELLCOUNT / 5 + 1 - i;
      invariant true
        && old(i) <= i
        && i <= 1 + CELLCOUNT / 5
        && (forall x₂₁: int ::
              ((exists i₂₀: int ::
                    if(x₂₁ == -2 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i else if(x₂₁ == -3 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i else if(x₂₁ == -4 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i else if(x₂₁ == -5 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i else x₂₁ == -1 + 5 * i₂₀ && old(i) <= i₂₀ && i₂₀ < i)
                 ==> (exists i₂₀: int ::
                          MINVAL <= CCCELVOL1
                          && i₂₀ <= CELLCOUNT / 5
                          && if(x₂₁ == -2 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == volArray[-1 + 5 * i₂₀ := CCCELVOL1][-2 + 5 * i₂₀] else if(x₂₁ == -3 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == volArray[-1 + 5 * i₂₀ := CCCELVOL1][-3 + 5 * i₂₀] else if(x₂₁ == -4 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == volArray[-1 + 5 * i₂₀ := CCCELVOL1][-4 + 5 * i₂₀] else if(x₂₁ == -5 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == volArray[-1 + 5 * i₂₀ := CCCELVOL1][-5 + 5 * i₂₀] else x₂₁ == -1 + 5 * i₂₀ && old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == CCCELVOL1)
                  || (exists i₂₀: int ::
                          !(MINVAL <= CCCELVOL1
                          )
                          && i₂₀ <= CELLCOUNT / 5
                          && if(x₂₁ == -2 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == volArray[-1 + 5 * i₂₀ := 0][-2 + 5 * i₂₀] else if(x₂₁ == -3 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == volArray[-1 + 5 * i₂₀ := 0][-3 + 5 * i₂₀] else if(x₂₁ == -4 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == volArray[-1 + 5 * i₂₀ := 0][-4 + 5 * i₂₀] else if(x₂₁ == -5 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == volArray[-1 + 5 * i₂₀ := 0][-5 + 5 * i₂₀] else x₂₁ == -1 + 5 * i₂₀ && old(i) <= i₂₀ && i₂₀ < i && volArray[x₂₁] == 0)))
        && (forall x₂₁: int ::
              (!((exists i₂₀: int ::
                    if(x₂₁ == -2 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i else if(x₂₁ == -3 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i else if(x₂₁ == -4 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i else if(x₂₁ == -5 + 5 * i₂₀) then old(i) <= i₂₀ && i₂₀ < i else x₂₁ == -1 + 5 * i₂₀ && old(i) <= i₂₀ && i₂₀ < i)
              )
                 ==> volArray[x₂₁] == old(volArray[x₂₁])))
        && (forall i₂₀: int ::
              (  old(i₂₀) <= i₂₀
                && old(i) <= i₂₀
                && i₂₀ < i
                 ==> i₂₀ <= CELLCOUNT / 5));
    {
      if(MINVAL <= CCCELVOL1) {
        volArray := volArray[i * 5 - 1 := CCCELVOL1];
      } else {
        volArray := volArray[i * 5 - 1 := 0];
      }
      volArray := volArray[i * 5 - 5 := volArray[i * 5 - 5]];
      volArray := volArray[i * 5 - 4 := volArray[i * 5 - 4]];
      volArray := volArray[i * 5 - 3 := volArray[i * 5 - 3]];
      volArray := volArray[i * 5 - 2 := volArray[i * 5 - 2]];
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT)
      decreases CELLCOUNT - i;
      invariant true
        && old(i) <= i
        && i <= CELLCOUNT
        && (forall i₂₄: int ::
              (  old(i₂₄) <= i₂₄
                && old(i) <= i₂₄
                && i₂₄ < i
                 ==> i₂₄ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

