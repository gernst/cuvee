(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (A) ((nil) (cons A (tail (Lst A)))))))

(declare-fun length ((Lst Elem)) Int)
(declare-fun reverse-accumulator ((Lst Elem) (Lst Elem)) (Lst Elem))

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
    ((zs (Lst Elem)))
    (=
      (reverse-accumulator nil zs)
      zs)))
(assert
  (forall
    ((zs (Lst Elem)) (y Elem) (ys (Lst Elem)))
    (=
      (reverse-accumulator (cons y ys) zs)
      (reverse-accumulator ys (cons y zs)))))