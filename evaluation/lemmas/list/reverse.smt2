(declare-datatypes
  ((nat 0))
  (((zero) (succ (pred nat)))))
(declare-datatypes
  ((list 0))
  (((nil)
      (cons (head nat) (tail list)))))
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
(declare-fun reverse (list) list)
(assert
  (= (reverse nil) nil))
(assert
  (forall
    ((y nat) (ys list))
    (=
      (reverse (cons y ys))
      (append (reverse ys) (cons y nil)))))
(declare-fun qreverse (list list) list)
(assert
  (forall
    ((zs list))
    (= (qreverse nil zs) zs)))
(assert
  (forall
    ((zs list) (y nat) (ys list))
    (=
      (qreverse (cons y ys) zs)
      (qreverse ys (cons y zs)))))
(declare-fun nreverse (list list) list)
(assert
  (forall
    ((zs list))
    (= (nreverse nil zs) zs)))
(assert
  (forall
    ((zs list) (y nat) (ys list))
    (=
      (nreverse (cons y ys) zs)
      (append (nreverse ys zs) (cons y nil)))))
