type elem;
data list<a> = nil | cons(head: a, tail: list<a>);

function append(xs: list<elem>, ys: list<elem>): list<elem>;

axiom forall ys: list<elem> ::
  append(nil, ys)
    == ys;

axiom forall x: elem, xs: list<elem>, ys: list<elem> ::
  append(cons(x,xs), ys)
    == cons(x, append(xs, ys));

goal forall xs: list<elem>, ys: list<elem>, zs: list<elem> ::
  append(append(xs, ys), zs)
    == append(xs, append(ys, zs))
proof induction xs {
  case nil => sorry
  case cons(h, t) => sorry
};