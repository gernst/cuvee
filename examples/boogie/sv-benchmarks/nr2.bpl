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
    var j: int;
    var volArray: [int]int;
    if(CELLCOUNT % 2 != 0) {
      c#result := 1;
      return;
    }
    assume CELLCOUNT % 2 == 0;
    i := 1;
    while(i <= CELLCOUNT / 2) {
      j := 2;
      while(1 <= j) {
        if(MINVAL <= j) {
          volArray := volArray[i * 2 - j := j];
        } else {
          volArray := volArray[i * 2 - j := 0];
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

