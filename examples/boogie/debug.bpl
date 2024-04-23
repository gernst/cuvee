data pyValue
  = pyNone
  | pyInt(pyGetInt: int)
  | pyBool(pyGetBool: bool)
  | pyArray(pyGetValues: [int]pyValue, pyGetLength: int)
  ;

type ref;
type field;

var heap:  [ref][field]pyValue;
var alloc: [ref][field]bool;

procedure __init__(self: ref, field: field)
    modifies heap, alloc;
{
    heap[self][field]  := pyNone;
    alloc[self][field] := true;
    // heap  := heap [self := heap[self] [field := pyNone]];
    // alloc := alloc[self := alloc[self][field := true]];
}