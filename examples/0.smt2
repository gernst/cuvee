(declare-sort Elem 0)

(declare-datatypes
  ((List 1))
  ((par (A) ((nil) (cons (head A) (tail (List A)))))))

(declare-fun length ((List Elem)) Int)
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