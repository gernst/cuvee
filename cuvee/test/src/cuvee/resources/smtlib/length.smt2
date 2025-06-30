(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (a) ((nil) (cons (head a) (tail (Lst a)))))))

(declare-fun append ((Lst Elem) (Lst Elem)) (Lst Elem))
(declare-fun length ((Lst Elem)) Int)

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
      (append nil zs)
      zs)))
(assert
  (forall
    ((zs (Lst Elem)) (y Elem) (ys (Lst Elem)))
    (=
      (append (cons y ys) zs)
      (cons y (append ys zs)))))