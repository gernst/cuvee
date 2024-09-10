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
    if(CELLCOUNT % 4 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 4 == 0;
    i := 1;
    while(i <= CELLCOUNT / 4) {
      j := 4;
      while(1 <= j) {
        if(MINVAL <= j) {
          volArray := volArray[i * 4 - j := j];
        } else {
          volArray := volArray[i * 4 - j := 0];
        }
        j := j - 1;
      }
      i := i + 1;
    }
    i := 0;
    while(i < CELLCOUNT) {
      assert MINVAL <= volArray[i] || volArray[i] == 0;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

