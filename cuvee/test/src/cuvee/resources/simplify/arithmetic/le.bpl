goal{:ex_true}  1 <= 1;
goal{:ex_true}  1 <= 2;
goal{:ex_false} 2 <= 1;

goal{:ex_true}  forall i: int :: i <= i;

goal{:ex_false} forall i: int :: i + 1 <= i;
goal{:ex_true}  forall i: int :: i <= i + 1;
