(declare-sort Elem 0)

(declare-datatypes
  ((List 1))
  ((par (a) ((nil) (cons (head a) (tail (List a)))))))

(declare-fun length ((List Elem)) Int)
(declare-fun append ((List Elem) (List Elem)) (List Elem))
(declare-fun reverse ((List Elem)) (List Elem))
(declare-fun map ((Array Elem Elem) (List Elem)) (List Elem))

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
  (=
    (reverse nil)
    nil))
(assert
  (forall
    ((y Elem) (ys (List Elem)))
    (=
      (reverse (cons y ys))
      (append (reverse ys) (cons y nil)))))