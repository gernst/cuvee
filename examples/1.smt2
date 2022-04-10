(declare-sort Elem 0)

(declare-datatypes
  ((Nat 0))
  (((zero) (succ (pred Nat)))))

(declare-datatypes
  ((List 1))
  ((par (A) ((nil) (cons (head A) (tail (List A)))))))

(declare-fun map ((Array Elem Elem) (List Elem)) (List Elem))
(declare-fun take (Nat (List Elem)) (List Elem))

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
    (take zero nil)
    nil))

(assert
  (forall
    ((y Elem) (ys (List Elem)))
    (=
      (take zero (cons y ys))
      nil)))

(assert
  (forall
    ((n Nat))
    (=
      (take (succ n) nil)
      nil)))

(assert
  (forall
    ((n Nat) (y Elem) (ys (List Elem)))
    (=
      (take (succ n) (cons y ys))
      (cons y (take n ys)))))
