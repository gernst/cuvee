function P(n: int): bool;

lemma forall x : int :: P(x)
proof induction x
  0     -> sorry,
  x + 1 -> sorry
end;