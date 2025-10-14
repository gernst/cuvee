function counter(n: int): Trace<int>;

free lemma {:rw} forall n: int ::
    current(counter(n)) == n;

goal forall n: int, ks: Trace<int> ::
    ks == counter(n) foo
        ==> current(map(for k <- ks yield k + 1)) == n + 1;
