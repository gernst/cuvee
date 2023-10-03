(declare-datatypes
  ((nat 0))
  (((zero) (succ (pred nat)))))
(declare-datatypes
  ((list 0))
  (((nil)
      (cons (head nat) (tail list)))))
(declare-fun add (nat nat) nat)
(assert
  (forall ((n nat)) (= (add zero n) n)))
(assert
  (forall
    ((m nat) (n nat))
    (= (add (succ m) n) (succ (add m n)))))
(declare-fun snoc (list nat) list)
(assert
  (forall
    ((z nat))
    (= (snoc nil z) (cons z nil))))
(assert
  (forall
    ((z nat) (y nat) (ys list))
    (= (snoc (cons y ys) z) (cons y (snoc ys z)))))
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
(declare-fun count (nat list) nat)
(assert
  (forall
    ((x nat))
    (= (count x nil) zero)))
(assert
  (forall
    ((x nat) (y nat) (ys list))
    (=
      (count x (cons y ys))
      (ite (= x y) (succ (count x ys)) (count x ys)))))
