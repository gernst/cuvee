(declare-sort Elem 0)

(declare-datatypes
  ((Nat 0))
  (((zero) (succ (pred Nat)))))

(declare-datatypes
  ((List 1))
  ((par (A) ((nil) (cons (head A) (tail (List A)))))))

(declare-fun length ((List Elem)) Nat)
(declare-fun map ((Array Elem Elem) (List Elem)) (List Elem))
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