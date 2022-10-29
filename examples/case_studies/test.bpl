data list<a> = nil | cons(head: a, tail: list<a>);

function P(x: list<int>, y: int): bool;

lemma forall x : list<int>, y : int :: P(x, y)
proof induction x
  nil         -> sorry,
  cons(a, xs) -> sorry
end;