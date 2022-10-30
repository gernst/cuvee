function add_two(x: int): int {
  x + 2
}

lemma forall x: int ::
  add_two(add_two(add_two(x))) == x + 6
proof
  unfold add_two at 1 , 3 then
  unfold add_two at 1 then
  sorry;