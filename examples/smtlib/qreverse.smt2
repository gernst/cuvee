(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (a) ((nil) (cons (head a) (tail (Lst a)))))))

(declare-fun qreverse ((Lst Elem) (Lst Elem)) (Lst Elem))

(assert
  (forall
    ((zs (Lst Elem)))
    (=
      (qreverse nil zs)
      zs)))
(assert
  (forall
    ((zs (Lst Elem)) (y Elem) (ys (Lst Elem)))
    (=
      (qreverse (cons y ys) zs)
      (qreverse ys (cons y zs)))))