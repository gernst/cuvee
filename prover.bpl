const A: bool;
const B: bool;
const C: bool;

// Should 
lemma A ==> A;
// Should
lemma A ==> !A;


lemma !(C && !B);