type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function length(xs: list<elem>): int;

const n: int;

axiom
  length(nil) == 0;
axiom forall x: elem, xs: list<elem> ::
  length(cons(x,xs)) == length(xs) + 1;

lemma forall xs: list<elem> ::
  length(xs) >= n
proof
  induction xs end;