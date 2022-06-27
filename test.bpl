const a: int;
const b: int;
const c: int;

lemma a > 0 && b > 0 && c > 0 && a * a + b * b == c * c;

const d: bool;
const e: bool;

lemma (d ==> e) ==> (!e ==> !d);

lemma !!d ==> d;

function p(x: int, y: int): bool;

const x: int;

axiom (x > 0);

lemma forall x : int :: (x == 0 <==> -x >= 0)
proof induction x
  zero    -> sorry,
  succ(x) -> sorry
end;

lemma (
    (exists y: int :: forall x: int :: p(x,y))
        ==> (forall x: int :: exists y: int :: p(x,y))
  );

lemma -a == a;

const bits: [int] bool;
