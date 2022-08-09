(declare-sort Elem 0)

(declare-datatypes
  ((Nat 0))
  (((zero) (succ (pred Nat)))))

(declare-datatypes
  ((Lst 1))
  ((par (A) ((nil) (cons A (tail (Lst A)))))))

(declare-fun map_take ((Array Elem Elem) Int (Lst Elem)) (Lst Elem))
(declare-fun take_map (Int (Array Elem Elem) (Lst Elem)) (Lst Elem))
(declare-fun drop_drop (Int Int (Lst Elem)) (Lst Elem))

(assert
  (forall
    ((n Int) (|f'| (Array Elem Elem)))
    (=
      (take_map n |f'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Elem)) (head57 Elem) (tail58 (Lst Elem)))
    (=
      (take_map n |f'| (cons head57 tail58))
      (ite
        (<= n 0)
        nil
        (cons (select |f'| head57) (take_map (- n 1) |f'| tail58))))))

(assert
  (forall
    ((f (Array Elem Elem)) (|n'| Int))
    (=
      (map_take f |n'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (|n'| Int) (head223 Elem) (tail224 (Lst Elem)))
    (=
      (map_take f |n'| (cons head223 tail224))
      (ite
        (<= |n'| 0)
        nil
        (cons (select f head223) (map_take f (- |n'| 1) tail224))))))

