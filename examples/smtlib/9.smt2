(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (A) ((nil) (cons (head A) (tail (Lst A)))))))

(declare-fun contains (Elem (Lst Elem)) Bool)

(assert
  (forall
    ((x Elem))
    (=
      (contains x nil)
      false)))
(assert
  (forall
    ((x Elem) (y Elem) (ys (Lst Elem)))
    (=
      (contains x (cons y ys))
      (or
        (=
          x
          y)
        (contains x ys)))))