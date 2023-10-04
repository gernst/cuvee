function not_(p: bool): bool;
axiom not_(false) == true;
axiom not_(true) == false;

lemma forall b: bool :: not_(not_(b)) == b;