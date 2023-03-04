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

lemma (x == 0 <==> -x >= 0);

lemma (
      (exists y: int :: forall x: int :: p(x,y))
  ==> (forall x: int :: exists y: int :: p(x,y))
);

lemma -a == a;

const bits: [int] bool;

function isSorted (list: [int] int, len: int) : bool {
  forall i: int :: 0 <= i && i + 1 < len ==> list[i] <= list[i + 1]
}

function f(i: int): int {
  if(i > 0) then f(i - 1) else 0
}