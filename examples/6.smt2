(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (A) ((nil) (cons A (tail (Lst A)))))))

;;; PREFIX!

(declare-fun app ((Lst Elem) (Lst Elem)) (Lst Elem))
(declare-fun pref ((Lst Elem) (Lst Elem)) Bool)
(assert (forall ((r (Lst Elem))) (= (app nil r) r)))
(assert (forall ((a Elem) (l (Lst Elem)) (r (Lst Elem))) (= (app (cons a l) r) (cons a (app l r)))))
(assert (forall ((x (Lst Elem))) (pref nil x)))
(assert (forall ((a Elem) (x (Lst Elem))) (not (pref (cons a x) nil))))
(assert (forall ((a Elem) (b Elem) (x (Lst Elem)) (y (Lst Elem))) (= (pref (cons a x) (cons b y)) (and (= a b) (pref x y)))))
; (assert (not (forall ((v0 (Lst Elem))) (pref (app (app v0 v0) (app (app v0 v0) v0)) (app (app (app v0 v0) v0) (app v0 v0))))))
; (check-sat)
