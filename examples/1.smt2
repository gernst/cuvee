(declare-sort Elem 0)

(declare-datatypes
  ((Nat 0))
  (((zero) (succ (pred Nat)))))

(declare-datatypes
  ((List 1))
  ((par (A) ((nil) (cons (head A) (tail (List A)))))))

(declare-fun take (Nat (List Elem)) (List Elem))

(assert
  (forall
    ((n Nat))
    (=
      (take n nil)
      nil)))

(assert
  (forall
    ((y Elem) (xs (List Elem)))
    (=
      (take zero xs)
      xs)))

(assert
  (forall
    ((n Nat) (y Elem) (ys (List Elem)))
    (=
      (take (succ n) (cons y ys))
      (cons y (take n ys)))))