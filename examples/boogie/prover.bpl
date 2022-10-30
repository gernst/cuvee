const A: bool;
const B: bool;
const C: bool;

axiom A;
lemma A && B ==> B;
lemma B ==> !A;
lemma C || (B ==> !A);