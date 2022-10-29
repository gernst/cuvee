(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (A) ((nil) (cons A (tail (Lst A)))))))

(declare-fun length ((Lst Elem)) Int)
(declare-fun append ((Lst Elem) (Lst Elem)) (Lst Elem))
(declare-fun reverse ((Lst Elem)) (Lst Elem))
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
(assert
  (=
    (reverse nil)
    nil))
(assert
  (forall
    ((y Elem) (ys (Lst Elem)))
    (=
      (reverse (cons y ys))
      (append (reverse ys) (cons y nil)))))