(declare-sort elem 0)
(declare-datatypes
  ((list 1))
  ((par
      (a)
      ((nil)
        (cons (head a) (tail (list a)))))))
(declare-fun
  eq
  ((list elem) (list elem))
  Bool)
(assert
  (=
    (eq (as nil (list elem)) (as nil (list elem)))
    true))
(assert
  (forall
    ((y elem) (ys (list elem)))
    (=
      (eq (as nil (list elem)) (cons y ys))
      false)))
(assert
  (forall
    ((x elem) (xs (list elem)))
    (=
      (eq (cons x xs) (as nil (list elem)))
      false)))
(assert
  (forall
    ((x elem) (xs (list elem)) (y elem) (ys (list elem)))
    (=
      (eq (cons x xs) (cons y ys))
      (and (= x y) (eq xs ys)))))
(declare-fun length ((list elem)) Int)
(declare-fun contains (elem (list elem)) Bool)
(declare-fun count (elem (list elem)) Int)
(declare-fun snoc ((list elem) elem) (list elem))
(declare-fun rotate (Int (list elem)) (list elem))
(declare-fun take (Int (list elem)) (list elem))
(declare-fun drop (Int (list elem)) (list elem))
(declare-fun reverse ((list elem)) (list elem))
(declare-fun
  reverseaccumulator
  ((list elem) (list elem))
  (list elem))
(declare-fun
  append
  ((list elem) (list elem))
  (list elem))
(declare-fun remove (elem (list elem)) (list elem))
(assert
  (=
    (length (as nil (list elem)))
    0))
(assert
  (forall
    ((x elem) (xs (list elem)))
    (= (length (cons x xs)) (+ (length xs) 1))))
(assert
  (forall
    ((x elem))
    (=
      (contains x (as nil (list elem)))
      false)))
(assert
  (forall
    ((x elem) (y elem) (ys (list elem)))
    (=
      (contains x (cons y ys))
      (or (= x y) (contains x ys)))))
(assert
  (forall
    ((x elem))
    (=
      (count x (as nil (list elem)))
      0)))
(assert
  (forall
    ((x elem) (y elem) (ys (list elem)))
    (=
      (count x (cons y ys))
      (ite (= x y) (+ (count x ys) 1) (count x ys)))))
(assert
  (forall
    ((z elem))
    (=
      (snoc (as nil (list elem)) z)
      (cons z (as nil (list elem))))))
(assert
  (forall
    ((z elem) (y elem) (ys (list elem)))
    (= (snoc (cons y ys) z) (cons y (snoc ys z)))))
(assert
  (forall
    ((n Int))
    (=
      (rotate n (as nil (list elem)))
      (as nil (list elem)))))
(assert
  (forall
    ((n Int) (y elem) (ys (list elem)))
    (=
      (rotate n (cons y ys))
      (ite
        (<= n 0)
        (cons y ys)
        (snoc (rotate (- n 1) ys) y)))))
(assert
  (forall
    ((n Int))
    (=
      (take n (as nil (list elem)))
      (as nil (list elem)))))
(assert
  (forall
    ((n Int) (y elem) (ys (list elem)))
    (=
      (take n (cons y ys))
      (ite
        (<= n 0)
        (as nil (list elem))
        (cons y (take (- n 1) ys))))))
(assert
  (forall
    ((n Int))
    (=
      (drop n (as nil (list elem)))
      (as nil (list elem)))))
(assert
  (forall
    ((n Int) (y elem) (ys (list elem)))
    (=
      (drop n (cons y ys))
      (ite (<= n 0) (cons y ys) (drop (- n 1) ys)))))
(assert
  (=
    (reverse (as nil (list elem)))
    (as nil (list elem))))
(assert
  (forall
    ((y elem) (ys (list elem)))
    (=
      (reverse (cons y ys))
      (snoc (reverse ys) y))))
(assert
  (forall
    ((zs (list elem)))
    (=
      (reverseaccumulator (as nil (list elem)) zs)
      zs)))
(assert
  (forall
    ((zs (list elem)) (y elem) (ys (list elem)))
    (=
      (reverseaccumulator (cons y ys) zs)
      (reverseaccumulator ys (cons y zs)))))
(assert
  (forall
    ((ys (list elem)))
    (=
      (append (as nil (list elem)) ys)
      ys)))
(assert
  (forall
    ((x elem) (xs (list elem)) (ys (list elem)))
    (=
      (append (cons x xs) ys)
      (cons x (append xs ys)))))
(assert
  (forall
    ((x elem))
    (=
      (remove x (as nil (list elem)))
      (as nil (list elem)))))
(assert
  (forall
    ((x elem) (y elem) (ys (list elem)))
    (=
      (remove x (cons y ys))
      (ite
        (= x y)
        (remove x ys)
        (cons y (remove x ys))))))
(lemma
  (forall ((xs (list elem))) (>= (length xs) 0)))
(lemma
  (forall
    ((xs (list elem)) (ys (list elem)) (zs (list elem)))
    (=
      (append (append xs ys) zs)
      (append xs (append ys zs)))))
(lemma
  (forall
    ((xs (list elem)) (ys (list elem)))
    (=
      (length (append xs ys))
      (+ (length xs) (length ys)))))
(lemma
  (forall
    ((xs (list elem)))
    (=
      (reverse (reverse xs))
      xs)))
(lemma
  (forall
    ((n Int) (xs (list elem)))
    (=
      (append (take n xs) (drop n xs))
      xs)))