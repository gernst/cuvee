data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var CELLCOUNT: int;

procedure main()
  returns (c#result: int)
  modifies CELLCOUNT;
{
  CELLCOUNT := 0;
  havoc CELLCOUNT;
  assume -2147483648 <= CELLCOUNT && CELLCOUNT < 2147483648;
  if(1 < CELLCOUNT) {
    var MINVAL: int := 2;
    var i: int;
    var j: int;
    var volArray: [int]int;
    if(CELLCOUNT % 3 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 3 == 0;
    i := 1;
    while(i <= CELLCOUNT / 3)
      decreases CELLCOUNT / 3 + 1 - i;
      invariant old(i) <= i
        && (forall i₉: int ::
              (  old(i) <= i₉
                && i₉ < i
                 ==> (exists volArray₆: [int]int, j₇: int ::
                        j₇ <= 3
                        && (forall j₅: int ::
                              (  j₇ < j₅
                                && j₅ <= 3
                                 ==> MINVAL <= j₅
                                    && 1 <= j₅
                                    && volArray₆[3 * i₉ + -j₅] == j₅
                                  ||   !(MINVAL <= j₅
                                    )
                                    && 1 <= j₅
                                    && volArray₆[3 * i₉ + -j₅] == 0))
                        && (forall j₅: int ::
                              (!(  j₇ < j₅
                                && j₅ <= 3
                              )
                                 ==> volArray₆[3 * i₉ + -j₅] == volArray[3 * i₉ + -j₅]))
                        && !(1 <= j₇
                        )
                        && i₉ <= CELLCOUNT / 3)));
    {
      j := 3;
      while(1 <= j)
        decreases j + 1 - 1;
        invariant j <= old(j)
          && (forall j₅: int ::
                (  j < j₅
                  && j₅ <= old(j)
                   ==> MINVAL <= j₅
                      && 1 <= j₅
                      && volArray[3 * i + -j₅] == j₅
                    ||   !(MINVAL <= j₅
                      )
                      && 1 <= j₅
                      && volArray[3 * i + -j₅] == 0))
          && (forall j₅: int ::
                (!(  j < j₅
                  && j₅ <= old(j)
                )
                   ==> volArray[3 * i + -j₅] == old(volArray)[3 * i + -j₅]));
      {
        if(MINVAL <= j) {
          volArray[((i * 3) - j)] := j;
        } else {
          volArray[((i * 3) - j)] := 0;
        }
        j := j - 1;
      }
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT)
      decreases CELLCOUNT - i;
      invariant old(i) <= i
        && (forall i₁₃: int ::
              (  old(i) <= i₁₃
                && i₁₃ < i
                 ==> i₁₃ < CELLCOUNT));
    {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

