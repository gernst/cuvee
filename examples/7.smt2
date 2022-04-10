(declare-sort Elem 0)

(declare-datatypes
  ((List 1))
  ((par (a) ((nil) (cons (head a) (tail (List a)))))))

(declare-fun length ((List Elem)) Int)
(declare-fun reverse-accumulator ((List Elem) (List Elem)) (List Elem))

(assert
  (=
    (length nil)
    0))
(assert
  (forall
    ((y Elem) (ys (List Elem)))
    (=
      (length (cons y ys))
      (+ 1 (length ys)))))

(assert
  (forall
    ((zs (List Elem)))
    (=
      (reverse-accumulator nil zs)
      zs)))
(assert
  (forall
    ((zs (List Elem)) (y Elem) (ys (List Elem)))
    (=
      (reverse-accumulator (cons y ys) zs)
      (reverse-accumulator ys (cons y zs)))))