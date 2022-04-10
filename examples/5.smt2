(set-logic ALL)
(declare-sort Elem 0)

(declare-datatypes
  ((List 1))
  ((par (a) ((nil) (cons (head a) (tail (List a)))))))

(declare-fun length  ((List Elem))     Int)
(declare-fun L ((List Elem) Int) Int)

(assert
  (=
    (length (as nil (List Elem)))
    0))
(assert
  (forall
    ((y Elem) (ys (List Elem)))
    (=
      (length (cons y ys))
      (+ 1 (length ys)))))

(assert
  (forall
    ((n Int))
      (=
        (L (as nil (List Elem)) n)
        n)))
(assert
  (forall
    ((y Elem) (ys (List Elem)) (n Int))
    (=
      (L (cons y ys) n)
      (L ys (+ n 1)))))

(assert
  (not (forall ((n Int) (ys (List Elem)))
    (= (+ n (length ys)) (L ys n)))))
(check-sat)