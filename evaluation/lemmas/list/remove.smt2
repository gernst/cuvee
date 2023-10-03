(declare-datatypes
  ((nat 0))
  (((zero) (succ (pred nat)))))
(declare-datatypes
  ((list 0))
  (((nil)
      (cons (head nat) (tail list)))))
(declare-fun not_ (Bool) Bool)
(assert
  (= (not_ false) true))
(assert
  (= (not_ true) false))
(declare-fun add (nat nat) nat)
(assert
  (forall ((n nat)) (= (add zero n) n)))
(assert
  (forall
    ((m nat) (n nat))
    (= (add (succ m) n) (succ (add m n)))))
(declare-fun sub (nat nat) nat)
(assert
  (forall ((m nat)) (= (sub m zero) m)))
(assert
  (forall
    ((n nat))
    (= (sub zero (succ n)) zero)))
(assert
  (forall
    ((m nat) (n nat))
    (=
      (sub (succ m) (succ n))
      (sub m n))))
(declare-fun length (list) nat)
(assert
  (= (length nil) zero))
(assert
  (forall
    ((x nat) (xs list))
    (= (length (cons x xs)) (succ (length xs)))))
(declare-fun contains (nat list) Bool)
(assert
  (forall
    ((x nat))
    (= (contains x nil) false)))
(assert
  (forall
    ((x nat) (y nat) (ys list))
    (=
      (contains x (cons y ys))
      (or (= x y) (contains x ys)))))
(declare-fun remove (nat list) list)
(assert
  (forall
    ((x nat))
    (= (remove x nil) nil)))
(assert
  (forall
    ((x nat) (y nat) (ys list))
    (=
      (remove x (cons y ys))
      (ite
        (= x y)
        (remove x ys)
        (cons y (remove x ys))))))
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
