(declare-sort Elem 0)

(declare-datatypes
  ((List 1))
  ((par (a) ((nil) (cons (head a) (tail (List a)))))))

;;; PREFIX!

(declare-fun app ((List Elem) (List Elem)) (List Elem))
(declare-fun pref ((List Elem) (List Elem)) Bool)
(assert (forall ((r (List Elem))) (= (app nil r) r)))
(assert (forall ((a Elem) (l (List Elem)) (r (List Elem))) (= (app (cons a l) r) (cons a (app l r)))))
(assert (forall ((x (List Elem))) (pref nil x)))
(assert (forall ((a Elem) (x (List Elem))) (not (pref (cons a x) nil))))
(assert (forall ((a Elem) (b Elem) (x (List Elem)) (y (List Elem))) (= (pref (cons a x) (cons b y)) (and (= a b) (pref x y)))))
; (assert (not (forall ((v0 (List Elem))) (pref (app (app v0 v0) (app (app v0 v0) v0)) (app (app (app v0 v0) v0) (app v0 v0))))))
; (check-sat)
