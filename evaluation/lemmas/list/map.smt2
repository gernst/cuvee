(declare-datatypes
  ((nat 0))
  (((zero) (succ (pred nat)))))
(declare-datatypes
  ((list 0))
  (((nil)
      (cons (head nat) (tail list)))))
(declare-fun leq (nat nat) Bool)
(assert
  (forall
    ((n nat))
    (= (leq zero n) true)))
(assert
  (forall
    ((m nat))
    (= (leq (succ m) zero) false)))
(assert
  (forall
    ((m nat) (n nat))
    (=
      (leq (succ m) (succ n))
      (leq m n))))
(declare-fun lt (nat nat) Bool)
(assert
  (forall
    ((m nat))
    (= (lt m zero) false)))
(assert
  (forall
    ((n nat))
    (= (lt zero (succ n)) true)))
(assert
  (forall
    ((m nat) (n nat))
    (=
      (lt (succ m) (succ n))
      (lt m n))))
(declare-fun length (list) nat)
(assert
  (= (length nil) zero))
(assert
  (forall
    ((x nat) (xs list))
    (= (length (cons x xs)) (succ (length xs)))))
(declare-fun append (list list) list)
(assert
  (forall
    ((ys list))
    (= (append nil ys) ys)))
(assert
  (forall
    ((x nat) (xs list) (ys list))
    (=
      (append (cons x xs) ys)
      (cons x (append xs ys)))))
(declare-fun
  map
  ((Array nat nat) list)
  list)
(assert
  (forall
    ((f (Array nat nat)))
    (= (map f nil) nil)))
(assert
  (forall
    ((f (Array nat nat)) (y nat) (ys list))
    (=
      (map f (cons y ys))
      (cons (select f y) (map f ys)))))
(declare-fun take (nat list) list)
(assert
  (forall ((n nat)) (= (take n nil) nil)))
(assert
  (forall
    ((y nat) (ys list))
    (=
      (take zero (cons y ys))
      nil)))
(assert
  (forall
    ((n nat) (y nat) (ys list))
    (=
      (take (succ n) (cons y ys))
      (cons y (take n ys)))))
(declare-fun drop (nat list) list)
(assert
  (forall ((n nat)) (= (drop n nil) nil)))
(assert
  (forall
    ((y nat) (ys list))
    (=
      (drop zero (cons y ys))
      (cons y ys))))
(assert
  (forall
    ((n nat) (y nat) (ys list))
    (=
      (drop (succ n) (cons y ys))
      (drop n ys))))
