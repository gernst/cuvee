(declare-sort Elem 0)

(declare-datatypes
  ((Lst 1))
  ((par (a) ((nil) (cons (head a) (tail (Lst a)))))))

(declare-fun length ((Lst Elem)) Int)
(declare-fun map ((Array Elem Elem) (Lst Elem)) (Lst Elem))
(declare-fun all ((Array Elem Bool) (Lst Elem)) Bool)
(declare-fun ex ((Array Elem Bool) (Lst Elem)) Bool)
(declare-fun contains (Elem (Lst Elem)) Bool)
(declare-fun count (Elem (Lst Elem)) Int)
(declare-fun snoc ((Lst Elem) Elem) (Lst Elem))
(declare-fun rotate (Int (Lst Elem)) (Lst Elem))
(declare-fun take (Int (Lst Elem)) (Lst Elem))
(declare-fun drop (Int (Lst Elem)) (Lst Elem))
(declare-fun reverse ((Lst Elem)) (Lst Elem))
(declare-fun reverse-accumulator ((Lst Elem) (Lst Elem)) (Lst Elem))
(declare-fun append ((Lst Elem) (Lst Elem)) (Lst Elem))
(declare-fun remove (Elem (Lst Elem)) (Lst Elem))
(declare-fun filter ((Array Elem Bool) (Lst Elem)) (Lst Elem))

(assert
  (=
    (length nil)
    0))
(assert
  (forall
    ((y Elem) (ys (Lst Elem)))
    (=
      (length (cons y ys))
      (+ 1 (length ys)))))
(assert
  (forall
    ((f (Array Elem Elem)))
    (=
      (map f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (y Elem) (ys (Lst Elem)))
    (=
      (map f (cons y ys))
      (cons (select f y) (map f ys)))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (all f nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (y Elem) (ys (Lst Elem)))
    (=
      (all f (cons y ys))
      (and
        (select f y)
        (all f ys)))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (ex f nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (y Elem) (ys (Lst Elem)))
    (=
      (ex f (cons y ys))
      (or
        (select f y)
        (ex f ys)))))
(assert
  (forall
    ((x Elem))
    (=
      (contains x nil)
      false)))
(assert
  (forall
    ((x Elem) (y Elem) (ys (Lst Elem)))
    (=
      (contains x (cons y ys))
      (or
        (=
          x
          y)
        (contains x ys)))))
(assert
  (forall
    ((x Elem))
    (=
      (count x nil)
      0)))
(assert
  (forall
    ((x Elem) (y Elem) (ys (Lst Elem)))
    (=
      (count x (cons y ys))
      (ite
        (=
          x
          y)
        (+ (count x ys) 1)
        (count x ys)))))
(assert
  (forall
    ((z Elem))
    (=
      (snoc nil z)
      (cons z nil))))
(assert
  (forall
    ((z Elem) (y Elem) (ys (Lst Elem)))
    (=
      (snoc (cons y ys) z)
      (cons y (snoc ys z)))))
(assert
  (forall
    ((n Int))
    (=
      (rotate n nil)
      nil)))
(assert
  (forall
    ((n Int) (y Elem) (ys (Lst Elem)))
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
      (take n nil)
      nil)))
(assert
  (forall
    ((n Int) (y Elem) (ys (Lst Elem)))
    (=
      (take n (cons y ys))
      (ite
        (<= n 0)
        nil
        (cons y (take (- n 1) ys))))))
(assert
  (forall
    ((n Int))
    (=
      (drop n nil)
      nil)))
(assert
  (forall
    ((n Int) (y Elem) (ys (Lst Elem)))
    (=
      (drop n (cons y ys))
      (ite
        (<= n 0)
        (cons y ys)
        (drop (- n 1) ys)))))
(assert
  (=
    (reverse nil)
    nil))
(assert
  (forall
    ((y Elem) (ys (Lst Elem)))
    (=
      (reverse (cons y ys))
      (append (reverse ys) (cons y nil)))))
(assert
  (forall
    ((zs (Lst Elem)))
    (=
      (reverse-accumulator nil zs)
      zs)))
(assert
  (forall
    ((zs (Lst Elem)) (y Elem) (ys (Lst Elem)))
    (=
      (reverse-accumulator (cons y ys) zs)
      (reverse-accumulator ys (cons y zs)))))
(assert
  (forall
    ((zs (Lst Elem)))
    (=
      (append nil zs)
      zs)))
(assert
  (forall
    ((zs (Lst Elem)) (y Elem) (ys (Lst Elem)))
    (=
      (append (cons y ys) zs)
      (cons y (append ys zs)))))
(assert
  (forall
    ((x Elem))
    (=
      (remove x nil)
      nil)))
(assert
  (forall
    ((x Elem) (y Elem) (ys (Lst Elem)))
    (=
      (remove x (cons y ys))
      (ite
        (=
          x
          y)
        (remove x ys)
        (cons y (remove x ys))))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (filter f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (y Elem) (ys (Lst Elem)))
    (=
      (filter f (cons y ys))
      (ite
        (select f y)
        (filter f ys)
        (cons y (filter f ys))))))
(check-sat)
