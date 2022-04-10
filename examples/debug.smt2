(declare-sort Elem 0)

(declare-datatypes
  ((List 1))
  ((par (a) ((nil) (cons (head a) (tail (List a)))))))

(declare-fun append ((List Elem) (List Elem)) (List Elem))

(assert
  (forall
    ((zs (List Elem)))
    (=
      (append nil zs)
      zs)))
(assert
  (forall
    ((zs (List Elem)) (y Elem) (ys (List Elem)))
    (=
      (append (cons y ys) zs)
      (cons y (append ys zs)))))