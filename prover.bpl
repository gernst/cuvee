function p(x: int, y: int): bool;
lemma (
      (exists y: int :: forall x: int :: p(x,y))
  ==> (forall x: int :: exists y: int :: p(x,y))
);