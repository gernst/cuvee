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
(declare-fun mul (nat nat) nat)
(assert
  (forall
    ((n nat))
    (= (mul zero n) zero)))
(assert
  (forall
    ((m nat) (n nat))
    (= (mul (succ m) n) (add n (mul m n)))))
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
(declare-fun sum (list) nat)
(assert (= (sum nil) zero))
(assert
  (forall
    ((n nat) (xs list))
    (= (sum (cons n xs)) (add n (sum xs)))))
(declare-fun is_runs (list list) Bool)
(assert
  (= (is_runs nil nil) true))
(assert
  (forall
    ((n nat) (ind list) (x nat) (val list))
    (=
      (is_runs (cons n ind) (cons x val))
      (is_runs ind val))))
(assert
  (forall
    ((n nat) (ind list))
    (=
      (is_runs (cons n ind) nil)
      false)))
(assert
  (forall
    ((ind list) (x nat) (val list))
    (=
      (is_runs nil (cons x val))
      false)))
(declare-fun sumruns (list list) nat)
(assert
  (= (sumruns nil nil) zero))
(assert
  (forall
    ((n nat) (ind list) (x nat) (val list))
    (=
      (sumruns (cons n ind) (cons x val))
      (add (mul n x) (sumruns ind val)))))
(assert
  (forall
    ((n nat) (ind list))
    (=
      (sumruns (cons n ind) nil)
      zero)))
(assert
  (forall
    ((ind list) (x nat) (val list))
    (=
      (sumruns nil (cons x val))
      zero)))
(declare-fun decode (list list) list)
(assert
  (= (decode nil nil) nil))
(assert
  (forall
    ((ind list) (x nat) (val list))
    (=
      (decode (cons zero ind) (cons x val))
      (decode ind val))))
(assert
  (forall
    ((n nat) (ind list) (x nat) (val list))
    (=
      (decode (cons (succ n) ind) (cons x val))
      (cons
        x
        (decode (cons n ind) (cons x val))))))
(assert
  (forall
    ((n nat) (ind list) (x nat) (val list))
    (=
      (decode (cons n ind) nil)
      nil)))
(assert
  (forall
    ((n nat) (ind list) (x nat) (val list))
    (=
      (decode nil (cons x val))
      nil)))
