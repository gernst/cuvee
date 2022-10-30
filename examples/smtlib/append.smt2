(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (a) ((nil) (cons (head a) (tail (Lst a)))))))

(declare-fun append ((Lst Elem) (Lst Elem)) (Lst Elem))
(declare-fun map ((Array Elem Elem) (Lst Elem)) (Lst Elem))

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