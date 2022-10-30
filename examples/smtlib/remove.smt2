(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (A) ((nil) (cons (head A) (tail (Lst A)))))))


(declare-fun append ((Lst Elem) (Lst Elem)) (Lst Elem))
(declare-fun remove (Elem (Lst Elem)) (Lst Elem))

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


(assert
  (forall
    ((x Elem))
    (=
      (remove x nil)
      nil)))
(assert
  (forall
    ((x Elem) (y Elem) (ys (Lst Elem)))
    (=
      (remove x (cons y ys))
      (ite
        (=
          x
          y)
        (remove x ys)
        (cons y (remove x ys))))))