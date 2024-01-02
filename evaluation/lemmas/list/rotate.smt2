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
(declare-fun add (nat nat) nat)
(assert
  (forall ((n nat)) (= (add zero n) n)))
(assert
  (forall
    ((m nat) (n nat))
    (= (add (succ m) n) (succ (add m n)))))
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
(declare-fun length (list) nat)
(assert
  (= (length nil) zero))
(assert
  (forall
    ((x nat) (xs list))
    (= (length (cons x xs)) (succ (length xs)))))
(declare-fun reverse (list) list)
(assert
  (= (reverse nil) nil))
(assert
  (forall
    ((y nat) (ys list))
    (=
      (reverse (cons y ys))
      (append (reverse ys) (cons y nil)))))
(declare-fun rotate (nat list) list)
(assert
  (forall
    ((n nat))
    (= (rotate n nil) nil)))
(assert
  (forall
    ((y nat) (ys list))
    (=
      (rotate zero (cons y ys))
      (cons y ys))))
(assert
  (forall
    ((n nat) (y nat) (ys list))
    (=
      (rotate (succ n) (cons y ys))
      (append (rotate n ys) (cons y nil)))))
