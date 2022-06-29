data list<a> = nil | cons(head: a, tail: list<a>);

function P(n: list<int>): bool;

lemma forall x : list<int> :: P(x)
proof induction x
  nil         -> sorry,
  cons(a, xs) -> sorry
end;