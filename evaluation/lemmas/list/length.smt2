(declare-datatypes
  ((nat 0))
  (((zero) (succ (pred nat)))))
(declare-datatypes
  ((list 0))
  (((nil)
      (cons (head nat) (tail list)))))
(declare-fun length (list) nat)
(assert
  (= (length nil) zero))
(assert
  (forall
    ((x nat) (xs list))
    (= (length (cons x xs)) (succ (length xs)))))
(declare-fun qlength (list nat) nat)
(assert
  (forall
    ((n nat))
    (= (qlength nil n) n)))
(assert
  (forall
    ((x nat) (xs list) (n nat))
    (=
      (qlength (cons x xs) n)
      (qlength xs (succ n)))))
(declare-fun nlength (list nat) nat)
(assert
  (forall
    ((n nat))
    (= (nlength nil n) n)))
(assert
  (forall
    ((x nat) (xs list) (n nat))
    (=
      (nlength (cons x xs) n)
      (succ (nlength xs n)))))
