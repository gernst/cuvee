const a: int;
const b: int;
const c: int;

lemma a > 0 && b > 0 && c > 0 && a * a + b * b == c * c;

const d: bool;
const e: bool;

lemma (d ==> e) ==> (!e ==> !d);