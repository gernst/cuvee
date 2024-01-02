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
(declare-fun length (list) nat)
(assert
  (= (length nil) zero))
(assert
  (forall
    ((x nat) (xs list))
    (= (length (cons x xs)) (succ (length xs)))))
(declare-fun
  filter
  ((Array nat Bool) list)
  list)
(assert
  (forall
    ((p (Array nat Bool)))
    (= (filter p nil) nil)))
(assert
  (forall
    ((p (Array nat Bool)) (y nat) (ys list))
    (=
      (filter p (cons y ys))
      (ite
        (select p y)
        (cons y (filter p ys))
        (filter p ys)))))
(declare-fun
  all
  ((Array nat Bool) list)
  Bool)
(assert
  (forall
    ((p (Array nat Bool)))
    (= (all p nil) true)))
(assert
  (forall
    ((p (Array nat Bool)) (y nat) (ys list))
    (=
      (all p (cons y ys))
      (and (select p y) (all p ys)))))
(declare-fun
  ex
  ((Array nat Bool) list)
  Bool)
(assert
  (forall
    ((p (Array nat Bool)))
    (= (ex p nil) false)))
(assert
  (forall
    ((p (Array nat Bool)) (y nat) (ys list))
    (=
      (ex p (cons y ys))
      (or (select p y) (ex p ys)))))
(declare-fun
  countif
  ((Array nat Bool) list)
  nat)
(assert
  (forall
    ((p (Array nat Bool)))
    (= (countif p nil) zero)))
(assert
  (forall
    ((p (Array nat Bool)) (y nat) (ys list))
    (=
      (countif p (cons y ys))
      (ite
        (select p y)
        (succ (countif p ys))
        (countif p ys)))))
