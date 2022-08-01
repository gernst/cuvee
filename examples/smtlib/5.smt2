(set-logic ALL)
(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (A) ((nil) (cons A (tail (Lst A)))))))

(declare-fun length  ((Lst Elem))     Int)
(declare-fun L ((Lst Elem) Int) Int)

(assert
  (=
    (length (as nil (Lst Elem)))
    0))
(assert
  (forall
    ((y Elem) (ys (Lst Elem)))
    (=
      (length (cons y ys))
      (+ 1 (length ys)))))

(assert
  (forall
    ((n Int))
      (=
        (L (as nil (Lst Elem)) n)
        n)))
(assert
  (forall
    ((y Elem) (ys (Lst Elem)) (n Int))
    (=
      (L (cons y ys) n)
      (L ys (+ n 1)))))

(assert
  (not (forall ((n Int) (ys (Lst Elem)))
    (= (+ n (length ys)) (L ys n)))))
(check-sat)