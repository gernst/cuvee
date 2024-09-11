function P(x: int, y: int): bool;

goal  (exists y: int :: forall x: int :: P(x, y))
  ==> (forall x: int :: exists y: int :: P(x, y));