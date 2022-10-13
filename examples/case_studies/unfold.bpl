function add_two(x: int): int {
  x + 2
}

lemma forall x: int ::
  add_two(add_two(x)) == x + 4
proof
  unfold add_two;