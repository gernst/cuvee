(declare-sort Elem 0)

(declare-datatypes
  ((List 1))
  ((par (A) ((nil) (cons (head A) (tail (List A)))))))

(declare-fun id ((List Elem)) (List Elem))
(declare-fun length ((List Elem)) Int)
(declare-fun map ((Array Elem Elem) (List Elem)) (List Elem))
(declare-fun append ((List Elem) (List Elem)) (List Elem))
(declare-fun remove (Elem (List Elem)) (List Elem))
(declare-fun contains (Elem (List Elem)) Bool)

(assert
  (=
    (id nil)
    nil))
(assert
  (forall
    ((y Elem) (ys (List Elem)))
    (=
      (id (cons y ys))
      (cons y (id ys)))))
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
    ((f (Array Elem Elem)))
    (=
      (map f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (y Elem) (ys (List Elem)))
    (=
      (map f (cons y ys))
      (cons (select f y) (map f ys)))))
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
(assert
  (forall
    ((x Elem))
    (=
      (remove x nil)
      nil)))
(assert
  (forall
    ((x Elem) (y Elem) (ys (List Elem)))
    (=
      (remove x (cons y ys))
      (ite
        (=
          x
          y)
        (remove x ys)
        (cons y (remove x ys))))))
(assert
  (forall
    ((x Elem))
    (=
      (contains x nil)
      false)))
(assert
  (forall
    ((x Elem) (y Elem) (ys (List Elem)))
    (=
      (contains x (cons y ys))
      (or
        (=
          x
          y)
        (contains x ys)))))