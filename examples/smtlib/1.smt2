(declare-sort Elem 0)

(declare-datatypes
  ((Nat 0))
  (((zero) (succ (pred Nat)))))

(declare-datatypes
  ((Lst 1))
  ((par (a) ((nil) (cons (head a) (tail (Lst a)))))))

(declare-fun map ((Array Elem Elem) (Lst Elem)) (Lst Elem))
(declare-fun take (Nat (Lst Elem)) (Lst Elem))

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
  (=
    (take zero nil)
    nil))

(assert
  (forall
    ((y Elem) (ys (Lst Elem)))
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
    ((n Nat) (y Elem) (ys (Lst Elem)))
    (=
      (take (succ n) (cons y ys))
      (cons y (take n ys)))))
