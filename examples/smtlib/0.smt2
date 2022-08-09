(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (A) ((nil) (cons A (tail (Lst A)))))))

(declare-fun length ((Lst Elem)) Int)
(declare-fun map ((Array Elem Elem) (Lst Elem)) (Lst Elem))

(assert
  (=
    (length nil)
    0))
(assert
  (forall
    ((y Elem) (ys (Lst Elem)))
    (=
      (length (cons y ys))
      (+ 1 (length ys)))))
(assert
  (forall
    ((f (Array Elem Elem)))
    (=
      (map f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (y Elem) (ys (Lst Elem)))
    (=
      (map f (cons y ys))
      (cons (select f y) (map f ys)))))