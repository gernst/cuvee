(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (A) ((nil) (cons (head A) (tail (Lst A)))))))

; (declare-fun id ((Lst Elem)) (Lst Elem))
(declare-fun length ((Lst Elem)) Int)
(declare-fun map ((Array Elem Elem) (Lst Elem)) (Lst Elem))
(declare-fun append ((Lst Elem) (Lst Elem)) (Lst Elem))
(declare-fun remove (Elem (Lst Elem)) (Lst Elem))
(declare-fun contains (Elem (Lst Elem)) Bool)

; (assert
;   (=
;     (id nil)
;     nil))
; (assert
;   (forall
;     ((y Elem) (ys (Lst Elem)))
;     (=
;       (id (cons y ys))
;       (cons y (id ys)))))
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
(assert
  (forall
    ((x Elem))
    (=
      (contains x nil)
      false)))
(assert
  (forall
    ((x Elem) (y Elem) (ys (Lst Elem)))
    (=
      (contains x (cons y ys))
      (or
        (=
          x
          y)
        (contains x ys)))))