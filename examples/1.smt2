(declare-sort Elem 0)

(declare-datatypes
  ((Nat 0))
  (((zero) (succ (pred Nat)))))

(declare-datatypes
  ((List 1))
  ((par (A) ((nil) (cons (head A) (tail (List A)))))))

(declare-fun length ((List Elem)) Nat)
(declare-fun take (Nat (List Elem)) (List Elem))
(declare-fun drop (Nat (List Elem)) (List Elem))

(assert
  (=
    (length nil)
    zero))
(assert
  (forall
    ((y Elem) (ys (List Elem)))
    (=
      (length (cons y ys))
      (succ (length ys)))))

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
      nil)))

(assert
  (forall
    ((n Nat) (y Elem) (ys (List Elem)))
    (=
      (take (succ n) (cons y ys))
      (cons y (take n ys)))))


(assert
  (forall
    ((n Nat))
    (=
      (drop n nil)
      nil)))

(assert
  (forall
    ((y Elem) (xs (List Elem)))
    (=
      (drop zero xs)
      xs)))

(assert
  (forall
    ((n Nat) (y Elem) (ys (List Elem)))
    (=
      (drop (succ n) (cons y ys))
      (drop n ys))))