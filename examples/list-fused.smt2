(declare-sort Elem 0)

(declare-datatypes
  ((List 1))
  ((par (A) ((nil) (cons (head A) (tail (List A)))))))

(declare-fun id ((List Elem)) (List Elem))
(declare-fun length ((List Elem)) Int)
(declare-fun map ((Array Elem Elem) (List Elem)) (List Elem))
(declare-fun all ((Array Elem Bool) (List Elem)) Bool)
(declare-fun ex ((Array Elem Bool) (List Elem)) Bool)
(declare-fun contains (Elem (List Elem)) Bool)
(declare-fun count (Elem (List Elem)) Int)
(declare-fun snoc ((List Elem) Elem) (List Elem))
(declare-fun rotate (Int (List Elem)) (List Elem))
(declare-fun take (Int (List Elem)) (List Elem))
(declare-fun drop (Int (List Elem)) (List Elem))
(declare-fun reverse ((List Elem)) (List Elem))
(declare-fun reverse-accumulator ((List Elem) (List Elem)) (List Elem))
(declare-fun append ((List Elem) (List Elem)) (List Elem))
(declare-fun remove (Elem (List Elem)) (List Elem))
(declare-fun filter ((Array Elem Bool) (List Elem)) (List Elem))
(declare-fun all_drop ((Array Elem Bool) Int (List Elem)) Bool)
(declare-fun all_take ((Array Elem Bool) Int (List Elem)) Bool)
(declare-fun all_snoc ((Array Elem Bool) (List Elem) Elem) Bool)
(declare-fun all_snoc__ ((Array Elem Bool) (List Elem)) Bool)
(declare-fun all_remove ((Array Elem Bool) Elem (List Elem)) Bool)
(declare-fun all_reverse-accumulator ((Array Elem Bool) (List Elem) (List Elem)) Bool)
(declare-fun all_rotate ((Array Elem Bool) Int (List Elem)) Bool)
(declare-fun all_reverse ((Array Elem Bool) (List Elem)) Bool)
(declare-fun all_filter ((Array Elem Bool) (Array Elem Bool) (List Elem)) Bool)
(declare-fun all_map ((Array Elem Bool) (Array Elem Elem) (List Elem)) Bool)
(declare-fun all_append ((Array Elem Bool) (List Elem) (List Elem)) Bool)
(declare-fun all_append__ ((Array Elem Bool) (List Elem)) Bool)
(declare-fun drop_drop (Int Int (List Elem)) (List Elem))
(declare-fun drop_take (Int Int (List Elem)) (List Elem))
(declare-fun drop_snoc (Int (List Elem) Elem) (List Elem))
(declare-fun drop_remove (Int Elem (List Elem)) (List Elem))
(declare-fun drop_reverse-accumulator (Int (List Elem) (List Elem)) (List Elem))
(declare-fun drop_rotate (Int Int (List Elem)) (List Elem))
(declare-fun drop_reverse (Int (List Elem)) (List Elem))
(declare-fun drop_filter (Int (Array Elem Bool) (List Elem)) (List Elem))
(declare-fun drop_map (Int (Array Elem Elem) (List Elem)) (List Elem))
(declare-fun drop_append (Int (List Elem) (List Elem)) (List Elem))
(declare-fun take_drop (Int Int (List Elem)) (List Elem))
(declare-fun take_take (Int Int (List Elem)) (List Elem))
(declare-fun take_snoc (Int (List Elem) Elem) (List Elem))
(declare-fun take_snoc__ (Int (List Elem)) (List Elem))
(declare-fun take_remove (Int Elem (List Elem)) (List Elem))
(declare-fun take_reverse-accumulator (Int (List Elem) (List Elem)) (List Elem))
(declare-fun take_rotate (Int Int (List Elem)) (List Elem))
(declare-fun take_reverse (Int (List Elem)) (List Elem))
(declare-fun take_filter (Int (Array Elem Bool) (List Elem)) (List Elem))
(declare-fun take_map (Int (Array Elem Elem) (List Elem)) (List Elem))
(declare-fun take_append (Int (List Elem) (List Elem)) (List Elem))
(declare-fun take_append__ (Int (List Elem)) (List Elem))
(declare-fun contains_drop (Elem Int (List Elem)) Bool)
(declare-fun contains_take (Elem Int (List Elem)) Bool)
(declare-fun contains_snoc (Elem (List Elem) Elem) Bool)
(declare-fun contains_snoc__ (Elem (List Elem)) Bool)
(declare-fun contains_remove (Elem Elem (List Elem)) Bool)
(declare-fun contains_reverse-accumulator (Elem (List Elem) (List Elem)) Bool)
(declare-fun contains_rotate (Elem Int (List Elem)) Bool)
(declare-fun contains_reverse (Elem (List Elem)) Bool)
(declare-fun contains_filter (Elem (Array Elem Bool) (List Elem)) Bool)
(declare-fun contains_map (Elem (Array Elem Elem) (List Elem)) Bool)
(declare-fun contains_append (Elem (List Elem) (List Elem)) Bool)
(declare-fun contains_append__ (Elem (List Elem)) Bool)
(declare-fun snoc_drop (Int (List Elem) Elem) (List Elem))
(declare-fun snoc_take (Int (List Elem) Elem) (List Elem))
(declare-fun snoc_take__ (Int (List Elem) Elem) (List Elem))
(declare-fun snoc_snoc ((List Elem) Elem Elem) (List Elem))
(declare-fun snoc_snoc__ ((List Elem)) (List Elem))
(declare-fun snoc_remove (Elem (List Elem) Elem) (List Elem))
(declare-fun snoc_remove__ (Elem (List Elem)) (List Elem))
(declare-fun snoc_reverse-accumulator ((List Elem) (List Elem) Elem) (List Elem))
(declare-fun snoc_rotate (Int (List Elem) Elem) (List Elem))
(declare-fun snoc_reverse ((List Elem) Elem) (List Elem))
(declare-fun snoc_filter ((Array Elem Bool) (List Elem) Elem) (List Elem))
(declare-fun snoc_filter__ ((Array Elem Bool) (List Elem)) (List Elem))
(declare-fun snoc_map ((Array Elem Elem) (List Elem) Elem) (List Elem))
(declare-fun snoc_map__ ((Array Elem Elem) (List Elem)) (List Elem))
(declare-fun snoc_append ((List Elem) (List Elem) Elem) (List Elem))
(declare-fun snoc_append__ ((List Elem)) (List Elem))
(declare-fun ex_drop ((Array Elem Bool) Int (List Elem)) Bool)
(declare-fun ex_take ((Array Elem Bool) Int (List Elem)) Bool)
(declare-fun ex_snoc ((Array Elem Bool) (List Elem) Elem) Bool)
(declare-fun ex_snoc__ ((Array Elem Bool) (List Elem)) Bool)
(declare-fun ex_remove ((Array Elem Bool) Elem (List Elem)) Bool)
(declare-fun ex_reverse-accumulator ((Array Elem Bool) (List Elem) (List Elem)) Bool)
(declare-fun ex_rotate ((Array Elem Bool) Int (List Elem)) Bool)
(declare-fun ex_reverse ((Array Elem Bool) (List Elem)) Bool)
(declare-fun ex_filter ((Array Elem Bool) (Array Elem Bool) (List Elem)) Bool)
(declare-fun ex_map ((Array Elem Bool) (Array Elem Elem) (List Elem)) Bool)
(declare-fun ex_append ((Array Elem Bool) (List Elem) (List Elem)) Bool)
(declare-fun ex_append__ ((Array Elem Bool) (List Elem)) Bool)
(declare-fun remove_drop (Elem Int (List Elem)) (List Elem))
(declare-fun remove_take (Elem Int (List Elem)) (List Elem))
(declare-fun remove_snoc (Elem (List Elem) Elem) (List Elem))
(declare-fun remove_snoc__ (Elem (List Elem)) (List Elem))
(declare-fun remove_remove (Elem Elem (List Elem)) (List Elem))
(declare-fun remove_reverse-accumulator (Elem (List Elem) (List Elem)) (List Elem))
(declare-fun remove_rotate (Elem Int (List Elem)) (List Elem))
(declare-fun remove_reverse (Elem (List Elem)) (List Elem))
(declare-fun remove_filter (Elem (Array Elem Bool) (List Elem)) (List Elem))
(declare-fun remove_map (Elem (Array Elem Elem) (List Elem)) (List Elem))
(declare-fun remove_append (Elem (List Elem) (List Elem)) (List Elem))
(declare-fun remove_append__ (Elem (List Elem)) (List Elem))
(declare-fun reverse-accumulator_drop (Int (List Elem) (List Elem)) (List Elem))
(declare-fun reverse-accumulator_take (Int (List Elem) (List Elem)) (List Elem))
(declare-fun reverse-accumulator_snoc ((List Elem) Elem (List Elem)) (List Elem))
(declare-fun reverse-accumulator_remove (Elem (List Elem) (List Elem)) (List Elem))
(declare-fun reverse-accumulator_reverse-accumulator ((List Elem) (List Elem) (List Elem)) (List Elem))
(declare-fun reverse-accumulator_rotate (Int (List Elem) (List Elem)) (List Elem))
(declare-fun reverse-accumulator_reverse ((List Elem) (List Elem)) (List Elem))
(declare-fun reverse-accumulator_filter ((Array Elem Bool) (List Elem) (List Elem)) (List Elem))
(declare-fun reverse-accumulator_map ((Array Elem Elem) (List Elem) (List Elem)) (List Elem))
(declare-fun reverse-accumulator_append ((List Elem) (List Elem) (List Elem)) (List Elem))
(declare-fun rotate_drop (Int Int (List Elem)) (List Elem))
(declare-fun rotate_take (Int Int (List Elem)) (List Elem))
(declare-fun rotate_snoc (Int (List Elem) Elem) (List Elem))
(declare-fun rotate_remove (Int Elem (List Elem)) (List Elem))
(declare-fun rotate_reverse-accumulator (Int (List Elem) (List Elem)) (List Elem))
(declare-fun rotate_rotate (Int Int (List Elem)) (List Elem))
(declare-fun rotate_reverse (Int (List Elem)) (List Elem))
(declare-fun rotate_filter (Int (Array Elem Bool) (List Elem)) (List Elem))
(declare-fun rotate_map (Int (Array Elem Elem) (List Elem)) (List Elem))
(declare-fun rotate_append (Int (List Elem) (List Elem)) (List Elem))
(declare-fun reverse_drop (Int (List Elem)) (List Elem))
(declare-fun reverse_take (Int (List Elem)) (List Elem))
(declare-fun reverse_snoc ((List Elem) Elem) (List Elem))
(declare-fun reverse_remove (Elem (List Elem)) (List Elem))
(declare-fun reverse_reverse-accumulator ((List Elem) (List Elem)) (List Elem))
(declare-fun reverse_rotate (Int (List Elem)) (List Elem))
(declare-fun reverse_reverse ((List Elem)) (List Elem))
(declare-fun reverse_filter ((Array Elem Bool) (List Elem)) (List Elem))
(declare-fun reverse_map ((Array Elem Elem) (List Elem)) (List Elem))
(declare-fun reverse_append ((List Elem) (List Elem)) (List Elem))
(declare-fun filter_drop ((Array Elem Bool) Int (List Elem)) (List Elem))
(declare-fun filter_take ((Array Elem Bool) Int (List Elem)) (List Elem))
(declare-fun filter_snoc ((Array Elem Bool) (List Elem) Elem) (List Elem))
(declare-fun filter_snoc__ ((Array Elem Bool) (List Elem)) (List Elem))
(declare-fun filter_remove ((Array Elem Bool) Elem (List Elem)) (List Elem))
(declare-fun filter_reverse-accumulator ((Array Elem Bool) (List Elem) (List Elem)) (List Elem))
(declare-fun filter_rotate ((Array Elem Bool) Int (List Elem)) (List Elem))
(declare-fun filter_reverse ((Array Elem Bool) (List Elem)) (List Elem))
(declare-fun filter_filter ((Array Elem Bool) (Array Elem Bool) (List Elem)) (List Elem))
(declare-fun filter_map ((Array Elem Bool) (Array Elem Elem) (List Elem)) (List Elem))
(declare-fun filter_append ((Array Elem Bool) (List Elem) (List Elem)) (List Elem))
(declare-fun filter_append__ ((Array Elem Bool) (List Elem)) (List Elem))
(declare-fun map_drop ((Array Elem Elem) Int (List Elem)) (List Elem))
(declare-fun map_take ((Array Elem Elem) Int (List Elem)) (List Elem))
(declare-fun map_snoc ((Array Elem Elem) (List Elem) Elem) (List Elem))
(declare-fun map_snoc__ ((Array Elem Elem) (List Elem)) (List Elem))
(declare-fun map_remove ((Array Elem Elem) Elem (List Elem)) (List Elem))
(declare-fun map_reverse-accumulator ((Array Elem Elem) (List Elem) (List Elem)) (List Elem))
(declare-fun map_rotate ((Array Elem Elem) Int (List Elem)) (List Elem))
(declare-fun map_reverse ((Array Elem Elem) (List Elem)) (List Elem))
(declare-fun map_filter ((Array Elem Elem) (Array Elem Bool) (List Elem)) (List Elem))
(declare-fun map_map ((Array Elem Elem) (Array Elem Elem) (List Elem)) (List Elem))
(declare-fun map_append ((Array Elem Elem) (List Elem) (List Elem)) (List Elem))
(declare-fun map_append__ ((Array Elem Elem) (List Elem)) (List Elem))
(declare-fun length_drop (Int (List Elem)) Int)
(declare-fun length_take (Int (List Elem)) Int)
(declare-fun length_snoc ((List Elem) Elem) Int)
(declare-fun length_snoc__ ((List Elem)) Int)
(declare-fun length_remove (Elem (List Elem)) Int)
(declare-fun length_reverse-accumulator ((List Elem) (List Elem)) Int)
(declare-fun length_rotate (Int (List Elem)) Int)
(declare-fun length_reverse ((List Elem)) Int)
(declare-fun length_filter ((Array Elem Bool) (List Elem)) Int)
(declare-fun length_map ((List Elem)) Int)
(declare-fun length_append ((List Elem) (List Elem)) Int)
(declare-fun length_append__ ((List Elem)) Int)
(declare-fun count_drop (Elem Int (List Elem)) Int)
(declare-fun count_take (Elem Int (List Elem)) Int)
(declare-fun count_snoc (Elem (List Elem) Elem) Int)
(declare-fun count_snoc__ (Elem (List Elem)) Int)
(declare-fun count_remove (Elem Elem (List Elem)) Int)
(declare-fun count_reverse-accumulator (Elem (List Elem) (List Elem)) Int)
(declare-fun count_rotate (Elem Int (List Elem)) Int)
(declare-fun count_reverse (Elem (List Elem)) Int)
(declare-fun count_filter (Elem (Array Elem Bool) (List Elem)) Int)
(declare-fun count_map (Elem (Array Elem Elem) (List Elem)) Int)
(declare-fun count_append (Elem (List Elem) (List Elem)) Int)
(declare-fun count_append__ (Elem (List Elem)) Int)
(declare-fun append_drop (Int (List Elem) (List Elem)) (List Elem))
(declare-fun append_take (Int (List Elem) (List Elem)) (List Elem))
(declare-fun append_take__ (Int (List Elem) (List Elem)) (List Elem))
(declare-fun append_snoc ((List Elem) Elem (List Elem)) (List Elem))
(declare-fun append_snoc__ ((List Elem)) (List Elem))
(declare-fun append_remove (Elem (List Elem) (List Elem)) (List Elem))
(declare-fun append_remove__ (Elem (List Elem)) (List Elem))
(declare-fun append_reverse-accumulator ((List Elem) (List Elem) (List Elem)) (List Elem))
(declare-fun append_rotate (Int (List Elem) (List Elem)) (List Elem))
(declare-fun append_reverse ((List Elem) (List Elem)) (List Elem))
(declare-fun append_filter ((Array Elem Bool) (List Elem) (List Elem)) (List Elem))
(declare-fun append_filter__ ((Array Elem Bool) (List Elem)) (List Elem))
(declare-fun append_map ((Array Elem Elem) (List Elem) (List Elem)) (List Elem))
(declare-fun append_map__ ((Array Elem Elem) (List Elem)) (List Elem))
(declare-fun append_append ((List Elem) (List Elem) (List Elem)) (List Elem))
(declare-fun append_append__ ((List Elem)) (List Elem))
(assert
  (=
    (id nil)
    nil))
(assert
  (forall
    ((y Elem) (ys (List Elem)))
    (=
      (id (cons y ys))
      (cons y (id ys)))))
(assert
  (=
    (length nil)
    0))
(assert
  (forall
    ((y Elem) (ys (List Elem)))
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
    ((f (Array Elem Elem)) (y Elem) (ys (List Elem)))
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
    ((f (Array Elem Bool)) (y Elem) (ys (List Elem)))
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
    ((f (Array Elem Bool)) (y Elem) (ys (List Elem)))
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
    ((x Elem) (y Elem) (ys (List Elem)))
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
    ((x Elem) (y Elem) (ys (List Elem)))
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
    ((z Elem) (y Elem) (ys (List Elem)))
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
    ((n Int) (y Elem) (ys (List Elem)))
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
    ((n Int) (y Elem) (ys (List Elem)))
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
    ((n Int) (y Elem) (ys (List Elem)))
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
    ((y Elem) (ys (List Elem)))
    (=
      (reverse (cons y ys))
      (snoc (reverse ys) y))))
(assert
  (forall
    ((zs (List Elem)))
    (=
      (reverse-accumulator nil zs)
      zs)))
(assert
  (forall
    ((zs (List Elem)) (y Elem) (ys (List Elem)))
    (=
      (reverse-accumulator (cons y ys) zs)
      (reverse-accumulator ys (cons y zs)))))
(assert
  (forall
    ((zs (List Elem)))
    (=
      (append nil zs)
      zs)))
(assert
  (forall
    ((zs (List Elem)) (y Elem) (ys (List Elem)))
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
    ((x Elem) (y Elem) (ys (List Elem)))
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
    ((f (Array Elem Bool)) (y Elem) (ys (List Elem)))
    (=
      (filter f (cons y ys))
      (ite
        (select f y)
        (filter f ys)
        (cons y (filter f ys))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int))
    (=
      (all_drop f |n'| nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int) (head1 Elem) (tail2 (List Elem)))
    (=
      (all_drop f |n'| (cons head1 tail2))
      (ite
        (<= |n'| 0)
        (and
          (select f head1)
          (all f tail2))
        (all_drop f (- |n'| 1) tail2)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int))
    (=
      (all_take f |n'| nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int) (head3 Elem) (tail4 (List Elem)))
    (=
      (all_take f |n'| (cons head3 tail4))
      (ite
        (<= |n'| 0)
        true
        (and
          (select f head3)
          (all_take f (- |n'| 1) tail4))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|z'| Elem))
    (=
      (all_snoc f nil |z'|)
      (and
        (select f |z'|)
        true))))
(assert
  (forall
    ((f (Array Elem Bool)) (|z'| Elem) (head5 Elem) (tail6 (List Elem)))
    (=
      (all_snoc f (cons head5 tail6) |z'|)
      (and
        (select f head5)
        (all_snoc f tail6 |z'|)))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (all_snoc__ f nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (head5 Elem) (tail6 (List Elem)))
    (=
      (all_snoc__ f (cons head5 tail6))
      (and
        (select f head5)
        (all_snoc__ f tail6)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|x'| Elem))
    (=
      (all_remove f |x'| nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (|x'| Elem) (head7 Elem) (tail8 (List Elem)))
    (=
      (all_remove f |x'| (cons head7 tail8))
      (ite
        (=
          |x'|
          head7)
        (all_remove f |x'| tail8)
        (and
          (select f head7)
          (all_remove f |x'| tail8))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)))
    (=
      (all_reverse-accumulator f nil |zs'|)
      (all f |zs'|))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)) (head9 Elem) (tail10 (List Elem)))
    (=
      (all_reverse-accumulator f (cons head9 tail10) |zs'|)
      (all_reverse-accumulator f tail10 (cons head9 |zs'|)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int))
    (=
      (all_rotate f |n'| nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int) (head11 Elem) (tail12 (List Elem)))
    (=
      (all_rotate f |n'| (cons head11 tail12))
      (ite
        (<= |n'| 0)
        (and
          (select f head11)
          (all f tail12))
        (all f (snoc (rotate (- |n'| 1) tail12) head11))))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (all_reverse f nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (head13 Elem) (tail14 (List Elem)))
    (=
      (all_reverse f (cons head13 tail14))
      (all f (snoc (reverse tail14) head13)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Bool)))
    (=
      (all_filter f |f'| nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Bool)) (head15 Elem) (tail16 (List Elem)))
    (=
      (all_filter f |f'| (cons head15 tail16))
      (ite
        (select |f'| head15)
        (all_filter f |f'| tail16)
        (and
          (select f head15)
          (all_filter f |f'| tail16))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Elem)))
    (=
      (all_map f |f'| nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Elem)) (head17 Elem) (tail18 (List Elem)))
    (=
      (all_map f |f'| (cons head17 tail18))
      (and
        (select f (select |f'| head17))
        (all_map f |f'| tail18)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)))
    (=
      (all_append f nil |zs'|)
      (all f |zs'|))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)) (head19 Elem) (tail20 (List Elem)))
    (=
      (all_append f (cons head19 tail20) |zs'|)
      (and
        (select f head19)
        (all_append f tail20 |zs'|)))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (all_append__ f nil)
      true)))
(assert
  (forall
    ((f (Array Elem Bool)) (head19 Elem) (tail20 (List Elem)))
    (=
      (all_append__ f (cons head19 tail20))
      (and
        (select f head19)
        (all_append__ f tail20)))))
(assert
  (forall
    ((n Int) (|n'| Int))
    (=
      (drop_drop n |n'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|n'| Int) (head21 Elem) (tail22 (List Elem)))
    (=
      (drop_drop n |n'| (cons head21 tail22))
      (ite
        (<= |n'| 0)
        (ite
          (<= n 0)
          (cons head21 tail22)
          (drop (- n 1) tail22))
        (drop_drop n (- |n'| 1) tail22)))))
(assert
  (forall
    ((n Int) (|n'| Int))
    (=
      (drop_take n |n'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|n'| Int) (head23 Elem) (tail24 (List Elem)))
    (=
      (drop_take n |n'| (cons head23 tail24))
      (ite
        (<= |n'| 0)
        nil
        (ite
          (<= n 0)
          (cons head23 (take (- |n'| 1) tail24))
          (drop_take (- n 1) (- |n'| 1) tail24))))))
(assert
  (forall
    ((n Int) (|z'| Elem))
    (=
      (drop_snoc n nil |z'|)
      (ite
        (<= n 0)
        (cons |z'| nil)
        nil))))
(assert
  (forall
    ((n Int) (|z'| Elem) (head25 Elem) (tail26 (List Elem)))
    (=
      (drop_snoc n (cons head25 tail26) |z'|)
      (ite
        (<= n 0)
        (cons head25 (snoc tail26 |z'|))
        (drop_snoc (- n 1) tail26 |z'|)))))
(assert
  (forall
    ((n Int) (|x'| Elem))
    (=
      (drop_remove n |x'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|x'| Elem) (head27 Elem) (tail28 (List Elem)))
    (=
      (drop_remove n |x'| (cons head27 tail28))
      (ite
        (=
          |x'|
          head27)
        (drop_remove n |x'| tail28)
        (ite
          (<= n 0)
          (cons head27 (remove |x'| tail28))
          (drop_remove (- n 1) |x'| tail28))))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)))
    (=
      (drop_reverse-accumulator n nil |zs'|)
      (drop n |zs'|))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)) (head29 Elem) (tail30 (List Elem)))
    (=
      (drop_reverse-accumulator n (cons head29 tail30) |zs'|)
      (drop_reverse-accumulator n tail30 (cons head29 |zs'|)))))
(assert
  (forall
    ((n Int) (|n'| Int))
    (=
      (drop_rotate n |n'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|n'| Int) (head31 Elem) (tail32 (List Elem)))
    (=
      (drop_rotate n |n'| (cons head31 tail32))
      (ite
        (<= |n'| 0)
        (ite
          (<= n 0)
          (cons head31 tail32)
          (drop (- n 1) tail32))
        (drop n (snoc (rotate (- |n'| 1) tail32) head31))))))
(assert
  (forall
    ((n Int))
    (=
      (drop_reverse n nil)
      nil)))
(assert
  (forall
    ((n Int) (head33 Elem) (tail34 (List Elem)))
    (=
      (drop_reverse n (cons head33 tail34))
      (drop n (snoc (reverse tail34) head33)))))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Bool)))
    (=
      (drop_filter n |f'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Bool)) (head35 Elem) (tail36 (List Elem)))
    (=
      (drop_filter n |f'| (cons head35 tail36))
      (ite
        (select |f'| head35)
        (drop_filter n |f'| tail36)
        (ite
          (<= n 0)
          (cons head35 (filter |f'| tail36))
          (drop_filter (- n 1) |f'| tail36))))))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Elem)))
    (=
      (drop_map n |f'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Elem)) (head37 Elem) (tail38 (List Elem)))
    (=
      (drop_map n |f'| (cons head37 tail38))
      (ite
        (<= n 0)
        (cons (select |f'| head37) (map |f'| tail38))
        (drop_map (- n 1) |f'| tail38)))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)))
    (=
      (drop_append n nil |zs'|)
      (drop n |zs'|))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)) (head39 Elem) (tail40 (List Elem)))
    (=
      (drop_append n (cons head39 tail40) |zs'|)
      (ite
        (<= n 0)
        (cons head39 (append tail40 |zs'|))
        (drop_append (- n 1) tail40 |zs'|)))))
(assert
  (forall
    ((n Int) (|n'| Int))
    (=
      (take_drop n |n'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|n'| Int) (head41 Elem) (tail42 (List Elem)))
    (=
      (take_drop n |n'| (cons head41 tail42))
      (ite
        (<= |n'| 0)
        (ite
          (<= n 0)
          nil
          (cons head41 (take (- n 1) tail42)))
        (take_drop n (- |n'| 1) tail42)))))
(assert
  (forall
    ((n Int) (|n'| Int))
    (=
      (take_take n |n'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|n'| Int) (head43 Elem) (tail44 (List Elem)))
    (=
      (take_take n |n'| (cons head43 tail44))
      (ite
        (<= |n'| 0)
        nil
        (ite
          (<= n 0)
          nil
          (cons head43 (take_take (- n 1) (- |n'| 1) tail44)))))))
(assert
  (forall
    ((n Int) (|z'| Elem))
    (=
      (take_snoc n nil |z'|)
      (ite
        (<= n 0)
        nil
        (cons |z'| nil)))))
(assert
  (forall
    ((n Int) (|z'| Elem) (head45 Elem) (tail46 (List Elem)))
    (=
      (take_snoc n (cons head45 tail46) |z'|)
      (ite
        (<= n 0)
        nil
        (cons head45 (take_snoc (- n 1) tail46 |z'|))))))
(assert
  (forall
    ((n Int))
    (=
      (take_snoc__ n nil)
      nil)))
(assert
  (forall
    ((n Int) (head45 Elem) (tail46 (List Elem)))
    (=
      (take_snoc__ n (cons head45 tail46))
      (ite
        (<= n 0)
        nil
        (cons head45 (take_snoc__ (- n 1) tail46))))))
(assert
  (forall
    ((n Int) (|x'| Elem))
    (=
      (take_remove n |x'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|x'| Elem) (head47 Elem) (tail48 (List Elem)))
    (=
      (take_remove n |x'| (cons head47 tail48))
      (ite
        (=
          |x'|
          head47)
        (take_remove n |x'| tail48)
        (ite
          (<= n 0)
          nil
          (cons head47 (take_remove (- n 1) |x'| tail48)))))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)))
    (=
      (take_reverse-accumulator n nil |zs'|)
      (take n |zs'|))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)) (head49 Elem) (tail50 (List Elem)))
    (=
      (take_reverse-accumulator n (cons head49 tail50) |zs'|)
      (take_reverse-accumulator n tail50 (cons head49 |zs'|)))))
(assert
  (forall
    ((n Int) (|n'| Int))
    (=
      (take_rotate n |n'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|n'| Int) (head51 Elem) (tail52 (List Elem)))
    (=
      (take_rotate n |n'| (cons head51 tail52))
      (ite
        (<= |n'| 0)
        (ite
          (<= n 0)
          nil
          (cons head51 (take (- n 1) tail52)))
        (take n (snoc (rotate (- |n'| 1) tail52) head51))))))
(assert
  (forall
    ((n Int))
    (=
      (take_reverse n nil)
      nil)))
(assert
  (forall
    ((n Int) (head53 Elem) (tail54 (List Elem)))
    (=
      (take_reverse n (cons head53 tail54))
      (take n (snoc (reverse tail54) head53)))))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Bool)))
    (=
      (take_filter n |f'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Bool)) (head55 Elem) (tail56 (List Elem)))
    (=
      (take_filter n |f'| (cons head55 tail56))
      (ite
        (select |f'| head55)
        (take_filter n |f'| tail56)
        (ite
          (<= n 0)
          nil
          (cons head55 (take_filter (- n 1) |f'| tail56)))))))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Elem)))
    (=
      (take_map n |f'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Elem)) (head57 Elem) (tail58 (List Elem)))
    (=
      (take_map n |f'| (cons head57 tail58))
      (ite
        (<= n 0)
        nil
        (cons (select |f'| head57) (take_map (- n 1) |f'| tail58))))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)))
    (=
      (take_append n nil |zs'|)
      (take n |zs'|))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)) (head59 Elem) (tail60 (List Elem)))
    (=
      (take_append n (cons head59 tail60) |zs'|)
      (ite
        (<= n 0)
        nil
        (cons head59 (take_append (- n 1) tail60 |zs'|))))))
(assert
  (forall
    ((n Int))
    (=
      (take_append__ n nil)
      nil)))
(assert
  (forall
    ((n Int) (head59 Elem) (tail60 (List Elem)))
    (=
      (take_append__ n (cons head59 tail60))
      (ite
        (<= n 0)
        nil
        (cons head59 (take_append__ (- n 1) tail60))))))
(assert
  (forall
    ((x Elem) (|n'| Int))
    (=
      (contains_drop x |n'| nil)
      false)))
(assert
  (forall
    ((x Elem) (|n'| Int) (head61 Elem) (tail62 (List Elem)))
    (=
      (contains_drop x |n'| (cons head61 tail62))
      (ite
        (<= |n'| 0)
        (or
          (=
            x
            head61)
          (contains x tail62))
        (contains_drop x (- |n'| 1) tail62)))))
(assert
  (forall
    ((x Elem) (|n'| Int))
    (=
      (contains_take x |n'| nil)
      false)))
(assert
  (forall
    ((x Elem) (|n'| Int) (head63 Elem) (tail64 (List Elem)))
    (=
      (contains_take x |n'| (cons head63 tail64))
      (ite
        (<= |n'| 0)
        false
        (or
          (=
            x
            head63)
          (contains_take x (- |n'| 1) tail64))))))
(assert
  (forall
    ((x Elem) (|z'| Elem))
    (=
      (contains_snoc x nil |z'|)
      (or
        (=
          x
          |z'|)
        false))))
(assert
  (forall
    ((x Elem) (|z'| Elem) (head65 Elem) (tail66 (List Elem)))
    (=
      (contains_snoc x (cons head65 tail66) |z'|)
      (or
        (=
          x
          head65)
        (contains_snoc x tail66 |z'|)))))
(assert
  (forall
    ((x Elem))
    (=
      (contains_snoc__ x nil)
      false)))
(assert
  (forall
    ((x Elem) (head65 Elem) (tail66 (List Elem)))
    (=
      (contains_snoc__ x (cons head65 tail66))
      (or
        (=
          x
          head65)
        (contains_snoc__ x tail66)))))
(assert
  (forall
    ((x Elem) (|x'| Elem))
    (=
      (contains_remove x |x'| nil)
      false)))
(assert
  (forall
    ((x Elem) (|x'| Elem) (head67 Elem) (tail68 (List Elem)))
    (=
      (contains_remove x |x'| (cons head67 tail68))
      (ite
        (=
          |x'|
          head67)
        (contains_remove x |x'| tail68)
        (or
          (=
            x
            head67)
          (contains_remove x |x'| tail68))))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)))
    (=
      (contains_reverse-accumulator x nil |zs'|)
      (contains x |zs'|))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)) (head69 Elem) (tail70 (List Elem)))
    (=
      (contains_reverse-accumulator x (cons head69 tail70) |zs'|)
      (contains_reverse-accumulator x tail70 (cons head69 |zs'|)))))
(assert
  (forall
    ((x Elem) (|n'| Int))
    (=
      (contains_rotate x |n'| nil)
      false)))
(assert
  (forall
    ((x Elem) (|n'| Int) (head71 Elem) (tail72 (List Elem)))
    (=
      (contains_rotate x |n'| (cons head71 tail72))
      (ite
        (<= |n'| 0)
        (or
          (=
            x
            head71)
          (contains x tail72))
        (contains x (snoc (rotate (- |n'| 1) tail72) head71))))))
(assert
  (forall
    ((x Elem))
    (=
      (contains_reverse x nil)
      false)))
(assert
  (forall
    ((x Elem) (head73 Elem) (tail74 (List Elem)))
    (=
      (contains_reverse x (cons head73 tail74))
      (contains x (snoc (reverse tail74) head73)))))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Bool)))
    (=
      (contains_filter x |f'| nil)
      false)))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Bool)) (head75 Elem) (tail76 (List Elem)))
    (=
      (contains_filter x |f'| (cons head75 tail76))
      (ite
        (select |f'| head75)
        (contains_filter x |f'| tail76)
        (or
          (=
            x
            head75)
          (contains_filter x |f'| tail76))))))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Elem)))
    (=
      (contains_map x |f'| nil)
      false)))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Elem)) (head77 Elem) (tail78 (List Elem)))
    (=
      (contains_map x |f'| (cons head77 tail78))
      (or
        (=
          x
          (select |f'| head77))
        (contains_map x |f'| tail78)))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)))
    (=
      (contains_append x nil |zs'|)
      (contains x |zs'|))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)) (head79 Elem) (tail80 (List Elem)))
    (=
      (contains_append x (cons head79 tail80) |zs'|)
      (or
        (=
          x
          head79)
        (contains_append x tail80 |zs'|)))))
(assert
  (forall
    ((x Elem))
    (=
      (contains_append__ x nil)
      false)))
(assert
  (forall
    ((x Elem) (head79 Elem) (tail80 (List Elem)))
    (=
      (contains_append__ x (cons head79 tail80))
      (or
        (=
          x
          head79)
        (contains_append__ x tail80)))))
(assert
  (forall
    ((|n'| Int) (z Elem))
    (=
      (snoc_drop |n'| nil z)
      (cons z nil))))
(assert
  (forall
    ((|n'| Int) (z Elem) (head81 Elem) (tail82 (List Elem)))
    (=
      (snoc_drop |n'| (cons head81 tail82) z)
      (ite
        (<= |n'| 0)
        (cons head81 (snoc tail82 z))
        (snoc_drop (- |n'| 1) tail82 z)))))
(assert
  (forall
    ((|n'| Int) (z Elem))
    (=
      (snoc_take |n'| nil z)
      (cons z nil))))
(assert
  (forall
    ((|n'| Int) (z Elem) (head83 Elem) (tail84 (List Elem)))
    (=
      (snoc_take |n'| (cons head83 tail84) z)
      (ite
        (<= |n'| 0)
        (cons z nil)
        (cons head83 (snoc_take (- |n'| 1) tail84 z))))))
(assert
  (forall
    ((|n'| Int) (z Elem))
    (=
      (snoc_take__ |n'| nil z)
      nil)))
(assert
  (forall
    ((|n'| Int) (z Elem) (head83 Elem) (tail84 (List Elem)))
    (=
      (snoc_take__ |n'| (cons head83 tail84) z)
      (ite
        (<= |n'| 0)
        (cons z nil)
        (cons head83 (snoc_take__ (- |n'| 1) tail84 z))))))
(assert
  (forall
    ((|z'| Elem) (z Elem))
    (=
      (snoc_snoc nil |z'| z)
      (cons |z'| (cons z nil)))))
(assert
  (forall
    ((|z'| Elem) (z Elem) (head85 Elem) (tail86 (List Elem)))
    (=
      (snoc_snoc (cons head85 tail86) |z'| z)
      (cons head85 (snoc_snoc tail86 |z'| z)))))
(assert
  (=
    (snoc_snoc__ nil)
    nil))
(assert
  (forall
    ((head85 Elem) (tail86 (List Elem)))
    (=
      (snoc_snoc__ (cons head85 tail86))
      (cons head85 (snoc_snoc__ tail86)))))
(assert
  (forall
    ((|x'| Elem) (z Elem))
    (=
      (snoc_remove |x'| nil z)
      (cons z nil))))
(assert
  (forall
    ((|x'| Elem) (z Elem) (head87 Elem) (tail88 (List Elem)))
    (=
      (snoc_remove |x'| (cons head87 tail88) z)
      (ite
        (=
          |x'|
          head87)
        (snoc_remove |x'| tail88 z)
        (cons head87 (snoc_remove |x'| tail88 z))))))
(assert
  (forall
    ((|x'| Elem))
    (=
      (snoc_remove__ |x'| nil)
      nil)))
(assert
  (forall
    ((|x'| Elem) (head87 Elem) (tail88 (List Elem)))
    (=
      (snoc_remove__ |x'| (cons head87 tail88))
      (ite
        (=
          |x'|
          head87)
        (snoc_remove__ |x'| tail88)
        (cons head87 (snoc_remove__ |x'| tail88))))))
(assert
  (forall
    ((|zs'| (List Elem)) (z Elem))
    (=
      (snoc_reverse-accumulator nil |zs'| z)
      (snoc |zs'| z))))
(assert
  (forall
    ((|zs'| (List Elem)) (z Elem) (head89 Elem) (tail90 (List Elem)))
    (=
      (snoc_reverse-accumulator (cons head89 tail90) |zs'| z)
      (snoc_reverse-accumulator tail90 (cons head89 |zs'|) z))))
(assert
  (forall
    ((|n'| Int) (z Elem))
    (=
      (snoc_rotate |n'| nil z)
      (cons z nil))))
(assert
  (forall
    ((|n'| Int) (z Elem) (head91 Elem) (tail92 (List Elem)))
    (=
      (snoc_rotate |n'| (cons head91 tail92) z)
      (ite
        (<= |n'| 0)
        (cons head91 (snoc tail92 z))
        (snoc (snoc_rotate (- |n'| 1) tail92 head91) z)))))
(assert
  (forall
    ((z Elem))
    (=
      (snoc_reverse nil z)
      (cons z nil))))
(assert
  (forall
    ((z Elem) (head93 Elem) (tail94 (List Elem)))
    (=
      (snoc_reverse (cons head93 tail94) z)
      (snoc (snoc_reverse tail94 head93) z))))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (z Elem))
    (=
      (snoc_filter |f'| nil z)
      (cons z nil))))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (z Elem) (head95 Elem) (tail96 (List Elem)))
    (=
      (snoc_filter |f'| (cons head95 tail96) z)
      (ite
        (select |f'| head95)
        (snoc_filter |f'| tail96 z)
        (cons head95 (snoc_filter |f'| tail96 z))))))
(assert
  (forall
    ((|f'| (Array Elem Bool)))
    (=
      (snoc_filter__ |f'| nil)
      nil)))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (head95 Elem) (tail96 (List Elem)))
    (=
      (snoc_filter__ |f'| (cons head95 tail96))
      (ite
        (select |f'| head95)
        (snoc_filter__ |f'| tail96)
        (cons head95 (snoc_filter__ |f'| tail96))))))
(assert
  (forall
    ((|f'| (Array Elem Elem)) (z Elem))
    (=
      (snoc_map |f'| nil z)
      (cons z nil))))
(assert
  (forall
    ((|f'| (Array Elem Elem)) (z Elem) (head97 Elem) (tail98 (List Elem)))
    (=
      (snoc_map |f'| (cons head97 tail98) z)
      (cons (select |f'| head97) (snoc_map |f'| tail98 z)))))
(assert
  (forall
    ((|f'| (Array Elem Elem)))
    (=
      (snoc_map__ |f'| nil)
      nil)))
(assert
  (forall
    ((|f'| (Array Elem Elem)) (head97 Elem) (tail98 (List Elem)))
    (=
      (snoc_map__ |f'| (cons head97 tail98))
      (cons (select |f'| head97) (snoc_map__ |f'| tail98)))))
(assert
  (forall
    ((|zs'| (List Elem)) (z Elem))
    (=
      (snoc_append nil |zs'| z)
      (snoc |zs'| z))))
(assert
  (forall
    ((|zs'| (List Elem)) (z Elem) (head99 Elem) (tail100 (List Elem)))
    (=
      (snoc_append (cons head99 tail100) |zs'| z)
      (cons head99 (snoc_append tail100 |zs'| z)))))
(assert
  (=
    (snoc_append__ nil)
    nil))
(assert
  (forall
    ((head99 Elem) (tail100 (List Elem)))
    (=
      (snoc_append__ (cons head99 tail100))
      (cons head99 (snoc_append__ tail100)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int))
    (=
      (ex_drop f |n'| nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int) (head101 Elem) (tail102 (List Elem)))
    (=
      (ex_drop f |n'| (cons head101 tail102))
      (ite
        (<= |n'| 0)
        (or
          (select f head101)
          (ex f tail102))
        (ex_drop f (- |n'| 1) tail102)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int))
    (=
      (ex_take f |n'| nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int) (head103 Elem) (tail104 (List Elem)))
    (=
      (ex_take f |n'| (cons head103 tail104))
      (ite
        (<= |n'| 0)
        false
        (or
          (select f head103)
          (ex_take f (- |n'| 1) tail104))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|z'| Elem))
    (=
      (ex_snoc f nil |z'|)
      (or
        (select f |z'|)
        false))))
(assert
  (forall
    ((f (Array Elem Bool)) (|z'| Elem) (head105 Elem) (tail106 (List Elem)))
    (=
      (ex_snoc f (cons head105 tail106) |z'|)
      (or
        (select f head105)
        (ex_snoc f tail106 |z'|)))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (ex_snoc__ f nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (head105 Elem) (tail106 (List Elem)))
    (=
      (ex_snoc__ f (cons head105 tail106))
      (or
        (select f head105)
        (ex_snoc__ f tail106)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|x'| Elem))
    (=
      (ex_remove f |x'| nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (|x'| Elem) (head107 Elem) (tail108 (List Elem)))
    (=
      (ex_remove f |x'| (cons head107 tail108))
      (ite
        (=
          |x'|
          head107)
        (ex_remove f |x'| tail108)
        (or
          (select f head107)
          (ex_remove f |x'| tail108))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)))
    (=
      (ex_reverse-accumulator f nil |zs'|)
      (ex f |zs'|))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)) (head109 Elem) (tail110 (List Elem)))
    (=
      (ex_reverse-accumulator f (cons head109 tail110) |zs'|)
      (ex_reverse-accumulator f tail110 (cons head109 |zs'|)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int))
    (=
      (ex_rotate f |n'| nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int) (head111 Elem) (tail112 (List Elem)))
    (=
      (ex_rotate f |n'| (cons head111 tail112))
      (ite
        (<= |n'| 0)
        (or
          (select f head111)
          (ex f tail112))
        (ex f (snoc (rotate (- |n'| 1) tail112) head111))))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (ex_reverse f nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (head113 Elem) (tail114 (List Elem)))
    (=
      (ex_reverse f (cons head113 tail114))
      (ex f (snoc (reverse tail114) head113)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Bool)))
    (=
      (ex_filter f |f'| nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Bool)) (head115 Elem) (tail116 (List Elem)))
    (=
      (ex_filter f |f'| (cons head115 tail116))
      (ite
        (select |f'| head115)
        (ex_filter f |f'| tail116)
        (or
          (select f head115)
          (ex_filter f |f'| tail116))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Elem)))
    (=
      (ex_map f |f'| nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Elem)) (head117 Elem) (tail118 (List Elem)))
    (=
      (ex_map f |f'| (cons head117 tail118))
      (or
        (select f (select |f'| head117))
        (ex_map f |f'| tail118)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)))
    (=
      (ex_append f nil |zs'|)
      (ex f |zs'|))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)) (head119 Elem) (tail120 (List Elem)))
    (=
      (ex_append f (cons head119 tail120) |zs'|)
      (or
        (select f head119)
        (ex_append f tail120 |zs'|)))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (ex_append__ f nil)
      false)))
(assert
  (forall
    ((f (Array Elem Bool)) (head119 Elem) (tail120 (List Elem)))
    (=
      (ex_append__ f (cons head119 tail120))
      (or
        (select f head119)
        (ex_append__ f tail120)))))
(assert
  (forall
    ((x Elem) (|n'| Int))
    (=
      (remove_drop x |n'| nil)
      nil)))
(assert
  (forall
    ((x Elem) (|n'| Int) (head121 Elem) (tail122 (List Elem)))
    (=
      (remove_drop x |n'| (cons head121 tail122))
      (ite
        (<= |n'| 0)
        (ite
          (=
            x
            head121)
          (remove x tail122)
          (cons head121 (remove x tail122)))
        (remove_drop x (- |n'| 1) tail122)))))
(assert
  (forall
    ((x Elem) (|n'| Int))
    (=
      (remove_take x |n'| nil)
      nil)))
(assert
  (forall
    ((x Elem) (|n'| Int) (head123 Elem) (tail124 (List Elem)))
    (=
      (remove_take x |n'| (cons head123 tail124))
      (ite
        (<= |n'| 0)
        nil
        (ite
          (=
            x
            head123)
          (remove_take x (- |n'| 1) tail124)
          (cons head123 (remove_take x (- |n'| 1) tail124)))))))
(assert
  (forall
    ((x Elem) (|z'| Elem))
    (=
      (remove_snoc x nil |z'|)
      (ite
        (=
          x
          |z'|)
        nil
        (cons |z'| nil)))))
(assert
  (forall
    ((x Elem) (|z'| Elem) (head125 Elem) (tail126 (List Elem)))
    (=
      (remove_snoc x (cons head125 tail126) |z'|)
      (ite
        (=
          x
          head125)
        (remove_snoc x tail126 |z'|)
        (cons head125 (remove_snoc x tail126 |z'|))))))
(assert
  (forall
    ((x Elem))
    (=
      (remove_snoc__ x nil)
      nil)))
(assert
  (forall
    ((x Elem) (head125 Elem) (tail126 (List Elem)))
    (=
      (remove_snoc__ x (cons head125 tail126))
      (ite
        (=
          x
          head125)
        (remove_snoc__ x tail126)
        (cons head125 (remove_snoc__ x tail126))))))
(assert
  (forall
    ((x Elem) (|x'| Elem))
    (=
      (remove_remove x |x'| nil)
      nil)))
(assert
  (forall
    ((x Elem) (|x'| Elem) (head127 Elem) (tail128 (List Elem)))
    (=
      (remove_remove x |x'| (cons head127 tail128))
      (ite
        (=
          |x'|
          head127)
        (remove_remove x |x'| tail128)
        (ite
          (=
            x
            head127)
          (remove_remove x |x'| tail128)
          (cons head127 (remove_remove x |x'| tail128)))))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)))
    (=
      (remove_reverse-accumulator x nil |zs'|)
      (remove x |zs'|))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)) (head129 Elem) (tail130 (List Elem)))
    (=
      (remove_reverse-accumulator x (cons head129 tail130) |zs'|)
      (remove_reverse-accumulator x tail130 (cons head129 |zs'|)))))
(assert
  (forall
    ((x Elem) (|n'| Int))
    (=
      (remove_rotate x |n'| nil)
      nil)))
(assert
  (forall
    ((x Elem) (|n'| Int) (head131 Elem) (tail132 (List Elem)))
    (=
      (remove_rotate x |n'| (cons head131 tail132))
      (ite
        (<= |n'| 0)
        (ite
          (=
            x
            head131)
          (remove x tail132)
          (cons head131 (remove x tail132)))
        (remove x (snoc (rotate (- |n'| 1) tail132) head131))))))
(assert
  (forall
    ((x Elem))
    (=
      (remove_reverse x nil)
      nil)))
(assert
  (forall
    ((x Elem) (head133 Elem) (tail134 (List Elem)))
    (=
      (remove_reverse x (cons head133 tail134))
      (remove x (snoc (reverse tail134) head133)))))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Bool)))
    (=
      (remove_filter x |f'| nil)
      nil)))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Bool)) (head135 Elem) (tail136 (List Elem)))
    (=
      (remove_filter x |f'| (cons head135 tail136))
      (ite
        (select |f'| head135)
        (remove_filter x |f'| tail136)
        (ite
          (=
            x
            head135)
          (remove_filter x |f'| tail136)
          (cons head135 (remove_filter x |f'| tail136)))))))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Elem)))
    (=
      (remove_map x |f'| nil)
      nil)))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Elem)) (head137 Elem) (tail138 (List Elem)))
    (=
      (remove_map x |f'| (cons head137 tail138))
      (ite
        (=
          x
          (select |f'| head137))
        (remove_map x |f'| tail138)
        (cons (select |f'| head137) (remove_map x |f'| tail138))))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)))
    (=
      (remove_append x nil |zs'|)
      (remove x |zs'|))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)) (head139 Elem) (tail140 (List Elem)))
    (=
      (remove_append x (cons head139 tail140) |zs'|)
      (ite
        (=
          x
          head139)
        (remove_append x tail140 |zs'|)
        (cons head139 (remove_append x tail140 |zs'|))))))
(assert
  (forall
    ((x Elem))
    (=
      (remove_append__ x nil)
      nil)))
(assert
  (forall
    ((x Elem) (head139 Elem) (tail140 (List Elem)))
    (=
      (remove_append__ x (cons head139 tail140))
      (ite
        (=
          x
          head139)
        (remove_append__ x tail140)
        (cons head139 (remove_append__ x tail140))))))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)))
    (=
      (reverse-accumulator_drop |n'| nil zs)
      zs)))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)) (head141 Elem) (tail142 (List Elem)))
    (=
      (reverse-accumulator_drop |n'| (cons head141 tail142) zs)
      (ite
        (<= |n'| 0)
        (reverse-accumulator tail142 (cons head141 zs))
        (reverse-accumulator_drop (- |n'| 1) tail142 zs)))))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)))
    (=
      (reverse-accumulator_take |n'| nil zs)
      zs)))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)) (head143 Elem) (tail144 (List Elem)))
    (=
      (reverse-accumulator_take |n'| (cons head143 tail144) zs)
      (ite
        (<= |n'| 0)
        zs
        (reverse-accumulator_take (- |n'| 1) tail144 (cons head143 zs))))))
(assert
  (forall
    ((|z'| Elem) (zs (List Elem)))
    (=
      (reverse-accumulator_snoc nil |z'| zs)
      (cons |z'| zs))))
(assert
  (forall
    ((|z'| Elem) (zs (List Elem)) (head145 Elem) (tail146 (List Elem)))
    (=
      (reverse-accumulator_snoc (cons head145 tail146) |z'| zs)
      (reverse-accumulator_snoc tail146 |z'| (cons head145 zs)))))
(assert
  (forall
    ((|x'| Elem) (zs (List Elem)))
    (=
      (reverse-accumulator_remove |x'| nil zs)
      zs)))
(assert
  (forall
    ((|x'| Elem) (zs (List Elem)) (head147 Elem) (tail148 (List Elem)))
    (=
      (reverse-accumulator_remove |x'| (cons head147 tail148) zs)
      (ite
        (=
          |x'|
          head147)
        (reverse-accumulator_remove |x'| tail148 zs)
        (reverse-accumulator_remove |x'| tail148 (cons head147 zs))))))
(assert
  (forall
    ((|zs'| (List Elem)) (zs (List Elem)))
    (=
      (reverse-accumulator_reverse-accumulator nil |zs'| zs)
      (reverse-accumulator |zs'| zs))))
(assert
  (forall
    ((|zs'| (List Elem)) (zs (List Elem)) (head149 Elem) (tail150 (List Elem)))
    (=
      (reverse-accumulator_reverse-accumulator (cons head149 tail150) |zs'| zs)
      (reverse-accumulator_reverse-accumulator tail150 (cons head149 |zs'|) zs))))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)))
    (=
      (reverse-accumulator_rotate |n'| nil zs)
      zs)))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)) (head151 Elem) (tail152 (List Elem)))
    (=
      (reverse-accumulator_rotate |n'| (cons head151 tail152) zs)
      (ite
        (<= |n'| 0)
        (reverse-accumulator tail152 (cons head151 zs))
        (reverse-accumulator (snoc (rotate (- |n'| 1) tail152) head151) zs)))))
(assert
  (forall
    ((zs (List Elem)))
    (=
      (reverse-accumulator_reverse nil zs)
      zs)))
(assert
  (forall
    ((zs (List Elem)) (head153 Elem) (tail154 (List Elem)))
    (=
      (reverse-accumulator_reverse (cons head153 tail154) zs)
      (reverse-accumulator (snoc (reverse tail154) head153) zs))))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (zs (List Elem)))
    (=
      (reverse-accumulator_filter |f'| nil zs)
      zs)))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (zs (List Elem)) (head155 Elem) (tail156 (List Elem)))
    (=
      (reverse-accumulator_filter |f'| (cons head155 tail156) zs)
      (ite
        (select |f'| head155)
        (reverse-accumulator_filter |f'| tail156 zs)
        (reverse-accumulator_filter |f'| tail156 (cons head155 zs))))))
(assert
  (forall
    ((|f'| (Array Elem Elem)) (zs (List Elem)))
    (=
      (reverse-accumulator_map |f'| nil zs)
      zs)))
(assert
  (forall
    ((|f'| (Array Elem Elem)) (zs (List Elem)) (head157 Elem) (tail158 (List Elem)))
    (=
      (reverse-accumulator_map |f'| (cons head157 tail158) zs)
      (reverse-accumulator_map |f'| tail158 (cons (select |f'| head157) zs)))))
(assert
  (forall
    ((|zs'| (List Elem)) (zs (List Elem)))
    (=
      (reverse-accumulator_append nil |zs'| zs)
      (reverse-accumulator |zs'| zs))))
(assert
  (forall
    ((|zs'| (List Elem)) (zs (List Elem)) (head159 Elem) (tail160 (List Elem)))
    (=
      (reverse-accumulator_append (cons head159 tail160) |zs'| zs)
      (reverse-accumulator_append tail160 |zs'| (cons head159 zs)))))
(assert
  (forall
    ((n Int) (|n'| Int))
    (=
      (rotate_drop n |n'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|n'| Int) (head161 Elem) (tail162 (List Elem)))
    (=
      (rotate_drop n |n'| (cons head161 tail162))
      (ite
        (<= |n'| 0)
        (ite
          (<= n 0)
          (cons head161 tail162)
          (snoc (rotate (- n 1) tail162) head161))
        (rotate_drop n (- |n'| 1) tail162)))))
(assert
  (forall
    ((n Int) (|n'| Int))
    (=
      (rotate_take n |n'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|n'| Int) (head163 Elem) (tail164 (List Elem)))
    (=
      (rotate_take n |n'| (cons head163 tail164))
      (ite
        (<= |n'| 0)
        nil
        (ite
          (<= n 0)
          (cons head163 (take (- |n'| 1) tail164))
          (snoc (rotate_take (- n 1) (- |n'| 1) tail164) head163))))))
(assert
  (forall
    ((n Int) (|z'| Elem))
    (=
      (rotate_snoc n nil |z'|)
      (ite
        (<= n 0)
        (cons |z'| nil)
        (cons |z'| nil)))))
(assert
  (forall
    ((n Int) (|z'| Elem) (head165 Elem) (tail166 (List Elem)))
    (=
      (rotate_snoc n (cons head165 tail166) |z'|)
      (ite
        (<= n 0)
        (cons head165 (snoc tail166 |z'|))
        (snoc (rotate_snoc (- n 1) tail166 |z'|) head165)))))
(assert
  (forall
    ((n Int) (|x'| Elem))
    (=
      (rotate_remove n |x'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|x'| Elem) (head167 Elem) (tail168 (List Elem)))
    (=
      (rotate_remove n |x'| (cons head167 tail168))
      (ite
        (=
          |x'|
          head167)
        (rotate_remove n |x'| tail168)
        (ite
          (<= n 0)
          (cons head167 (remove |x'| tail168))
          (snoc (rotate_remove (- n 1) |x'| tail168) head167))))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)))
    (=
      (rotate_reverse-accumulator n nil |zs'|)
      (rotate n |zs'|))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)) (head169 Elem) (tail170 (List Elem)))
    (=
      (rotate_reverse-accumulator n (cons head169 tail170) |zs'|)
      (rotate_reverse-accumulator n tail170 (cons head169 |zs'|)))))
(assert
  (forall
    ((n Int) (|n'| Int))
    (=
      (rotate_rotate n |n'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|n'| Int) (head171 Elem) (tail172 (List Elem)))
    (=
      (rotate_rotate n |n'| (cons head171 tail172))
      (ite
        (<= |n'| 0)
        (ite
          (<= n 0)
          (cons head171 tail172)
          (snoc (rotate (- n 1) tail172) head171))
        (rotate n (snoc (rotate (- |n'| 1) tail172) head171))))))
(assert
  (forall
    ((n Int))
    (=
      (rotate_reverse n nil)
      nil)))
(assert
  (forall
    ((n Int) (head173 Elem) (tail174 (List Elem)))
    (=
      (rotate_reverse n (cons head173 tail174))
      (rotate n (snoc (reverse tail174) head173)))))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Bool)))
    (=
      (rotate_filter n |f'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Bool)) (head175 Elem) (tail176 (List Elem)))
    (=
      (rotate_filter n |f'| (cons head175 tail176))
      (ite
        (select |f'| head175)
        (rotate_filter n |f'| tail176)
        (ite
          (<= n 0)
          (cons head175 (filter |f'| tail176))
          (snoc (rotate_filter (- n 1) |f'| tail176) head175))))))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Elem)))
    (=
      (rotate_map n |f'| nil)
      nil)))
(assert
  (forall
    ((n Int) (|f'| (Array Elem Elem)) (head177 Elem) (tail178 (List Elem)))
    (=
      (rotate_map n |f'| (cons head177 tail178))
      (ite
        (<= n 0)
        (cons (select |f'| head177) (map |f'| tail178))
        (snoc (rotate_map (- n 1) |f'| tail178) (select |f'| head177))))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)))
    (=
      (rotate_append n nil |zs'|)
      (rotate n |zs'|))))
(assert
  (forall
    ((n Int) (|zs'| (List Elem)) (head179 Elem) (tail180 (List Elem)))
    (=
      (rotate_append n (cons head179 tail180) |zs'|)
      (ite
        (<= n 0)
        (cons head179 (append tail180 |zs'|))
        (snoc (rotate_append (- n 1) tail180 |zs'|) head179)))))
(assert
  (forall
    ((|n'| Int))
    (=
      (reverse_drop |n'| nil)
      nil)))
(assert
  (forall
    ((|n'| Int) (head181 Elem) (tail182 (List Elem)))
    (=
      (reverse_drop |n'| (cons head181 tail182))
      (ite
        (<= |n'| 0)
        (snoc (reverse tail182) head181)
        (reverse_drop (- |n'| 1) tail182)))))
(assert
  (forall
    ((|n'| Int))
    (=
      (reverse_take |n'| nil)
      nil)))
(assert
  (forall
    ((|n'| Int) (head183 Elem) (tail184 (List Elem)))
    (=
      (reverse_take |n'| (cons head183 tail184))
      (ite
        (<= |n'| 0)
        nil
        (snoc (reverse_take (- |n'| 1) tail184) head183)))))
(assert
  (forall
    ((|z'| Elem))
    (=
      (reverse_snoc nil |z'|)
      (cons |z'| nil))))
(assert
  (forall
    ((|z'| Elem) (head185 Elem) (tail186 (List Elem)))
    (=
      (reverse_snoc (cons head185 tail186) |z'|)
      (snoc (reverse_snoc tail186 |z'|) head185))))
(assert
  (forall
    ((|x'| Elem))
    (=
      (reverse_remove |x'| nil)
      nil)))
(assert
  (forall
    ((|x'| Elem) (head187 Elem) (tail188 (List Elem)))
    (=
      (reverse_remove |x'| (cons head187 tail188))
      (ite
        (=
          |x'|
          head187)
        (reverse_remove |x'| tail188)
        (snoc (reverse_remove |x'| tail188) head187)))))
(assert
  (forall
    ((|zs'| (List Elem)))
    (=
      (reverse_reverse-accumulator nil |zs'|)
      (reverse |zs'|))))
(assert
  (forall
    ((|zs'| (List Elem)) (head189 Elem) (tail190 (List Elem)))
    (=
      (reverse_reverse-accumulator (cons head189 tail190) |zs'|)
      (reverse_reverse-accumulator tail190 (cons head189 |zs'|)))))
(assert
  (forall
    ((|n'| Int))
    (=
      (reverse_rotate |n'| nil)
      nil)))
(assert
  (forall
    ((|n'| Int) (head191 Elem) (tail192 (List Elem)))
    (=
      (reverse_rotate |n'| (cons head191 tail192))
      (ite
        (<= |n'| 0)
        (snoc (reverse tail192) head191)
        (reverse (snoc (rotate (- |n'| 1) tail192) head191))))))
(assert
  (=
    (reverse_reverse nil)
    nil))
(assert
  (forall
    ((head193 Elem) (tail194 (List Elem)))
    (=
      (reverse_reverse (cons head193 tail194))
      (reverse (snoc (reverse tail194) head193)))))
(assert
  (forall
    ((|f'| (Array Elem Bool)))
    (=
      (reverse_filter |f'| nil)
      nil)))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (head195 Elem) (tail196 (List Elem)))
    (=
      (reverse_filter |f'| (cons head195 tail196))
      (ite
        (select |f'| head195)
        (reverse_filter |f'| tail196)
        (snoc (reverse_filter |f'| tail196) head195)))))
(assert
  (forall
    ((|f'| (Array Elem Elem)))
    (=
      (reverse_map |f'| nil)
      nil)))
(assert
  (forall
    ((|f'| (Array Elem Elem)) (head197 Elem) (tail198 (List Elem)))
    (=
      (reverse_map |f'| (cons head197 tail198))
      (snoc (reverse_map |f'| tail198) (select |f'| head197)))))
(assert
  (forall
    ((|zs'| (List Elem)))
    (=
      (reverse_append nil |zs'|)
      (reverse |zs'|))))
(assert
  (forall
    ((|zs'| (List Elem)) (head199 Elem) (tail200 (List Elem)))
    (=
      (reverse_append (cons head199 tail200) |zs'|)
      (snoc (reverse_append tail200 |zs'|) head199))))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int))
    (=
      (filter_drop f |n'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int) (head201 Elem) (tail202 (List Elem)))
    (=
      (filter_drop f |n'| (cons head201 tail202))
      (ite
        (<= |n'| 0)
        (ite
          (select f head201)
          (filter f tail202)
          (cons head201 (filter f tail202)))
        (filter_drop f (- |n'| 1) tail202)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int))
    (=
      (filter_take f |n'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int) (head203 Elem) (tail204 (List Elem)))
    (=
      (filter_take f |n'| (cons head203 tail204))
      (ite
        (<= |n'| 0)
        nil
        (ite
          (select f head203)
          (filter_take f (- |n'| 1) tail204)
          (cons head203 (filter_take f (- |n'| 1) tail204)))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|z'| Elem))
    (=
      (filter_snoc f nil |z'|)
      (ite
        (select f |z'|)
        nil
        (cons |z'| nil)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|z'| Elem) (head205 Elem) (tail206 (List Elem)))
    (=
      (filter_snoc f (cons head205 tail206) |z'|)
      (ite
        (select f head205)
        (filter_snoc f tail206 |z'|)
        (cons head205 (filter_snoc f tail206 |z'|))))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (filter_snoc__ f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (head205 Elem) (tail206 (List Elem)))
    (=
      (filter_snoc__ f (cons head205 tail206))
      (ite
        (select f head205)
        (filter_snoc__ f tail206)
        (cons head205 (filter_snoc__ f tail206))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|x'| Elem))
    (=
      (filter_remove f |x'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (|x'| Elem) (head207 Elem) (tail208 (List Elem)))
    (=
      (filter_remove f |x'| (cons head207 tail208))
      (ite
        (=
          |x'|
          head207)
        (filter_remove f |x'| tail208)
        (ite
          (select f head207)
          (filter_remove f |x'| tail208)
          (cons head207 (filter_remove f |x'| tail208)))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)))
    (=
      (filter_reverse-accumulator f nil |zs'|)
      (filter f |zs'|))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)) (head209 Elem) (tail210 (List Elem)))
    (=
      (filter_reverse-accumulator f (cons head209 tail210) |zs'|)
      (filter_reverse-accumulator f tail210 (cons head209 |zs'|)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int))
    (=
      (filter_rotate f |n'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (|n'| Int) (head211 Elem) (tail212 (List Elem)))
    (=
      (filter_rotate f |n'| (cons head211 tail212))
      (ite
        (<= |n'| 0)
        (ite
          (select f head211)
          (filter f tail212)
          (cons head211 (filter f tail212)))
        (filter f (snoc (rotate (- |n'| 1) tail212) head211))))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (filter_reverse f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (head213 Elem) (tail214 (List Elem)))
    (=
      (filter_reverse f (cons head213 tail214))
      (filter f (snoc (reverse tail214) head213)))))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Bool)))
    (=
      (filter_filter f |f'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Bool)) (head215 Elem) (tail216 (List Elem)))
    (=
      (filter_filter f |f'| (cons head215 tail216))
      (ite
        (select |f'| head215)
        (filter_filter f |f'| tail216)
        (ite
          (select f head215)
          (filter_filter f |f'| tail216)
          (cons head215 (filter_filter f |f'| tail216)))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Elem)))
    (=
      (filter_map f |f'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (|f'| (Array Elem Elem)) (head217 Elem) (tail218 (List Elem)))
    (=
      (filter_map f |f'| (cons head217 tail218))
      (ite
        (select f (select |f'| head217))
        (filter_map f |f'| tail218)
        (cons (select |f'| head217) (filter_map f |f'| tail218))))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)))
    (=
      (filter_append f nil |zs'|)
      (filter f |zs'|))))
(assert
  (forall
    ((f (Array Elem Bool)) (|zs'| (List Elem)) (head219 Elem) (tail220 (List Elem)))
    (=
      (filter_append f (cons head219 tail220) |zs'|)
      (ite
        (select f head219)
        (filter_append f tail220 |zs'|)
        (cons head219 (filter_append f tail220 |zs'|))))))
(assert
  (forall
    ((f (Array Elem Bool)))
    (=
      (filter_append__ f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Bool)) (head219 Elem) (tail220 (List Elem)))
    (=
      (filter_append__ f (cons head219 tail220))
      (ite
        (select f head219)
        (filter_append__ f tail220)
        (cons head219 (filter_append__ f tail220))))))
(assert
  (forall
    ((f (Array Elem Elem)) (|n'| Int))
    (=
      (map_drop f |n'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (|n'| Int) (head221 Elem) (tail222 (List Elem)))
    (=
      (map_drop f |n'| (cons head221 tail222))
      (ite
        (<= |n'| 0)
        (cons (select f head221) (map f tail222))
        (map_drop f (- |n'| 1) tail222)))))
(assert
  (forall
    ((f (Array Elem Elem)) (|n'| Int))
    (=
      (map_take f |n'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (|n'| Int) (head223 Elem) (tail224 (List Elem)))
    (=
      (map_take f |n'| (cons head223 tail224))
      (ite
        (<= |n'| 0)
        nil
        (cons (select f head223) (map_take f (- |n'| 1) tail224))))))
(assert
  (forall
    ((f (Array Elem Elem)) (|z'| Elem))
    (=
      (map_snoc f nil |z'|)
      (cons (select f |z'|) nil))))
(assert
  (forall
    ((f (Array Elem Elem)) (|z'| Elem) (head225 Elem) (tail226 (List Elem)))
    (=
      (map_snoc f (cons head225 tail226) |z'|)
      (cons (select f head225) (map_snoc f tail226 |z'|)))))
(assert
  (forall
    ((f (Array Elem Elem)))
    (=
      (map_snoc__ f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (head225 Elem) (tail226 (List Elem)))
    (=
      (map_snoc__ f (cons head225 tail226))
      (cons (select f head225) (map_snoc__ f tail226)))))
(assert
  (forall
    ((f (Array Elem Elem)) (|x'| Elem))
    (=
      (map_remove f |x'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (|x'| Elem) (head227 Elem) (tail228 (List Elem)))
    (=
      (map_remove f |x'| (cons head227 tail228))
      (ite
        (=
          |x'|
          head227)
        (map_remove f |x'| tail228)
        (cons (select f head227) (map_remove f |x'| tail228))))))
(assert
  (forall
    ((f (Array Elem Elem)) (|zs'| (List Elem)))
    (=
      (map_reverse-accumulator f nil |zs'|)
      (map f |zs'|))))
(assert
  (forall
    ((f (Array Elem Elem)) (|zs'| (List Elem)) (head229 Elem) (tail230 (List Elem)))
    (=
      (map_reverse-accumulator f (cons head229 tail230) |zs'|)
      (map_reverse-accumulator f tail230 (cons head229 |zs'|)))))
(assert
  (forall
    ((f (Array Elem Elem)) (|n'| Int))
    (=
      (map_rotate f |n'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (|n'| Int) (head231 Elem) (tail232 (List Elem)))
    (=
      (map_rotate f |n'| (cons head231 tail232))
      (ite
        (<= |n'| 0)
        (cons (select f head231) (map f tail232))
        (map f (snoc (rotate (- |n'| 1) tail232) head231))))))
(assert
  (forall
    ((f (Array Elem Elem)))
    (=
      (map_reverse f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (head233 Elem) (tail234 (List Elem)))
    (=
      (map_reverse f (cons head233 tail234))
      (map f (snoc (reverse tail234) head233)))))
(assert
  (forall
    ((f (Array Elem Elem)) (|f'| (Array Elem Bool)))
    (=
      (map_filter f |f'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (|f'| (Array Elem Bool)) (head235 Elem) (tail236 (List Elem)))
    (=
      (map_filter f |f'| (cons head235 tail236))
      (ite
        (select |f'| head235)
        (map_filter f |f'| tail236)
        (cons (select f head235) (map_filter f |f'| tail236))))))
(assert
  (forall
    ((f (Array Elem Elem)) (|f'| (Array Elem Elem)))
    (=
      (map_map f |f'| nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (|f'| (Array Elem Elem)) (head237 Elem) (tail238 (List Elem)))
    (=
      (map_map f |f'| (cons head237 tail238))
      (cons (select f (select |f'| head237)) (map_map f |f'| tail238)))))
(assert
  (forall
    ((f (Array Elem Elem)) (|zs'| (List Elem)))
    (=
      (map_append f nil |zs'|)
      (map f |zs'|))))
(assert
  (forall
    ((f (Array Elem Elem)) (|zs'| (List Elem)) (head239 Elem) (tail240 (List Elem)))
    (=
      (map_append f (cons head239 tail240) |zs'|)
      (cons (select f head239) (map_append f tail240 |zs'|)))))
(assert
  (forall
    ((f (Array Elem Elem)))
    (=
      (map_append__ f nil)
      nil)))
(assert
  (forall
    ((f (Array Elem Elem)) (head239 Elem) (tail240 (List Elem)))
    (=
      (map_append__ f (cons head239 tail240))
      (cons (select f head239) (map_append__ f tail240)))))
(assert
  (forall
    ((|n'| Int))
    (=
      (length_drop |n'| nil)
      0)))
(assert
  (forall
    ((|n'| Int) (head241 Elem) (tail242 (List Elem)))
    (=
      (length_drop |n'| (cons head241 tail242))
      (ite
        (<= |n'| 0)
        (+ 1 (length tail242))
        (length_drop (- |n'| 1) tail242)))))
(assert
  (forall
    ((|n'| Int))
    (=
      (length_take |n'| nil)
      0)))
(assert
  (forall
    ((|n'| Int) (head243 Elem) (tail244 (List Elem)))
    (=
      (length_take |n'| (cons head243 tail244))
      (ite
        (<= |n'| 0)
        0
        (+ 1 (length_take (- |n'| 1) tail244))))))
(assert
  (forall
    ((|z'| Elem))
    (=
      (length_snoc nil |z'|)
      (+ 1 0))))
(assert
  (forall
    ((|z'| Elem) (head245 Elem) (tail246 (List Elem)))
    (=
      (length_snoc (cons head245 tail246) |z'|)
      (+ 1 (length_snoc tail246 |z'|)))))
(assert
  (=
    (length_snoc__ nil)
    0))
(assert
  (forall
    ((head245 Elem) (tail246 (List Elem)))
    (=
      (length_snoc__ (cons head245 tail246))
      (+ 1 (length_snoc__ tail246)))))
(assert
  (forall
    ((|x'| Elem))
    (=
      (length_remove |x'| nil)
      0)))
(assert
  (forall
    ((|x'| Elem) (head247 Elem) (tail248 (List Elem)))
    (=
      (length_remove |x'| (cons head247 tail248))
      (ite
        (=
          |x'|
          head247)
        (length_remove |x'| tail248)
        (+ 1 (length_remove |x'| tail248))))))
(assert
  (forall
    ((|zs'| (List Elem)))
    (=
      (length_reverse-accumulator nil |zs'|)
      (length |zs'|))))
(assert
  (forall
    ((|zs'| (List Elem)) (head249 Elem) (tail250 (List Elem)))
    (=
      (length_reverse-accumulator (cons head249 tail250) |zs'|)
      (length_reverse-accumulator tail250 (cons head249 |zs'|)))))
(assert
  (forall
    ((|n'| Int))
    (=
      (length_rotate |n'| nil)
      0)))
(assert
  (forall
    ((|n'| Int) (head251 Elem) (tail252 (List Elem)))
    (=
      (length_rotate |n'| (cons head251 tail252))
      (ite
        (<= |n'| 0)
        (+ 1 (length tail252))
        (length (snoc (rotate (- |n'| 1) tail252) head251))))))
(assert
  (=
    (length_reverse nil)
    0))
(assert
  (forall
    ((head253 Elem) (tail254 (List Elem)))
    (=
      (length_reverse (cons head253 tail254))
      (length (snoc (reverse tail254) head253)))))
(assert
  (forall
    ((|f'| (Array Elem Bool)))
    (=
      (length_filter |f'| nil)
      0)))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (head255 Elem) (tail256 (List Elem)))
    (=
      (length_filter |f'| (cons head255 tail256))
      (ite
        (select |f'| head255)
        (length_filter |f'| tail256)
        (+ 1 (length_filter |f'| tail256))))))
(assert
  (=
    (length_map nil)
    0))
(assert
  (forall
    ((head257 Elem) (tail258 (List Elem)))
    (=
      (length_map (cons head257 tail258))
      (+ 1 (length_map tail258)))))
(assert
  (forall
    ((|zs'| (List Elem)))
    (=
      (length_append nil |zs'|)
      (length |zs'|))))
(assert
  (forall
    ((|zs'| (List Elem)) (head259 Elem) (tail260 (List Elem)))
    (=
      (length_append (cons head259 tail260) |zs'|)
      (+ 1 (length_append tail260 |zs'|)))))
(assert
  (=
    (length_append__ nil)
    0))
(assert
  (forall
    ((head259 Elem) (tail260 (List Elem)))
    (=
      (length_append__ (cons head259 tail260))
      (+ 1 (length_append__ tail260)))))
(assert
  (forall
    ((x Elem) (|n'| Int))
    (=
      (count_drop x |n'| nil)
      0)))
(assert
  (forall
    ((x Elem) (|n'| Int) (head261 Elem) (tail262 (List Elem)))
    (=
      (count_drop x |n'| (cons head261 tail262))
      (ite
        (<= |n'| 0)
        (ite
          (=
            x
            head261)
          (+ (count x tail262) 1)
          (count x tail262))
        (count_drop x (- |n'| 1) tail262)))))
(assert
  (forall
    ((x Elem) (|n'| Int))
    (=
      (count_take x |n'| nil)
      0)))
(assert
  (forall
    ((x Elem) (|n'| Int) (head263 Elem) (tail264 (List Elem)))
    (=
      (count_take x |n'| (cons head263 tail264))
      (ite
        (<= |n'| 0)
        0
        (ite
          (=
            x
            head263)
          (+ (count_take x (- |n'| 1) tail264) 1)
          (count_take x (- |n'| 1) tail264))))))
(assert
  (forall
    ((x Elem) (|z'| Elem))
    (=
      (count_snoc x nil |z'|)
      (ite
        (=
          x
          |z'|)
        (+ 0 1)
        0))))
(assert
  (forall
    ((x Elem) (|z'| Elem) (head265 Elem) (tail266 (List Elem)))
    (=
      (count_snoc x (cons head265 tail266) |z'|)
      (ite
        (=
          x
          head265)
        (+ (count_snoc x tail266 |z'|) 1)
        (count_snoc x tail266 |z'|)))))
(assert
  (forall
    ((x Elem))
    (=
      (count_snoc__ x nil)
      0)))
(assert
  (forall
    ((x Elem) (head265 Elem) (tail266 (List Elem)))
    (=
      (count_snoc__ x (cons head265 tail266))
      (ite
        (=
          x
          head265)
        (+ (count_snoc__ x tail266) 1)
        (count_snoc__ x tail266)))))
(assert
  (forall
    ((x Elem) (|x'| Elem))
    (=
      (count_remove x |x'| nil)
      0)))
(assert
  (forall
    ((x Elem) (|x'| Elem) (head267 Elem) (tail268 (List Elem)))
    (=
      (count_remove x |x'| (cons head267 tail268))
      (ite
        (=
          |x'|
          head267)
        (count_remove x |x'| tail268)
        (ite
          (=
            x
            head267)
          (+ (count_remove x |x'| tail268) 1)
          (count_remove x |x'| tail268))))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)))
    (=
      (count_reverse-accumulator x nil |zs'|)
      (count x |zs'|))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)) (head269 Elem) (tail270 (List Elem)))
    (=
      (count_reverse-accumulator x (cons head269 tail270) |zs'|)
      (count_reverse-accumulator x tail270 (cons head269 |zs'|)))))
(assert
  (forall
    ((x Elem) (|n'| Int))
    (=
      (count_rotate x |n'| nil)
      0)))
(assert
  (forall
    ((x Elem) (|n'| Int) (head271 Elem) (tail272 (List Elem)))
    (=
      (count_rotate x |n'| (cons head271 tail272))
      (ite
        (<= |n'| 0)
        (ite
          (=
            x
            head271)
          (+ (count x tail272) 1)
          (count x tail272))
        (count x (snoc (rotate (- |n'| 1) tail272) head271))))))
(assert
  (forall
    ((x Elem))
    (=
      (count_reverse x nil)
      0)))
(assert
  (forall
    ((x Elem) (head273 Elem) (tail274 (List Elem)))
    (=
      (count_reverse x (cons head273 tail274))
      (count x (snoc (reverse tail274) head273)))))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Bool)))
    (=
      (count_filter x |f'| nil)
      0)))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Bool)) (head275 Elem) (tail276 (List Elem)))
    (=
      (count_filter x |f'| (cons head275 tail276))
      (ite
        (select |f'| head275)
        (count_filter x |f'| tail276)
        (ite
          (=
            x
            head275)
          (+ (count_filter x |f'| tail276) 1)
          (count_filter x |f'| tail276))))))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Elem)))
    (=
      (count_map x |f'| nil)
      0)))
(assert
  (forall
    ((x Elem) (|f'| (Array Elem Elem)) (head277 Elem) (tail278 (List Elem)))
    (=
      (count_map x |f'| (cons head277 tail278))
      (ite
        (=
          x
          (select |f'| head277))
        (+ (count_map x |f'| tail278) 1)
        (count_map x |f'| tail278)))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)))
    (=
      (count_append x nil |zs'|)
      (count x |zs'|))))
(assert
  (forall
    ((x Elem) (|zs'| (List Elem)) (head279 Elem) (tail280 (List Elem)))
    (=
      (count_append x (cons head279 tail280) |zs'|)
      (ite
        (=
          x
          head279)
        (+ (count_append x tail280 |zs'|) 1)
        (count_append x tail280 |zs'|)))))
(assert
  (forall
    ((x Elem))
    (=
      (count_append__ x nil)
      0)))
(assert
  (forall
    ((x Elem) (head279 Elem) (tail280 (List Elem)))
    (=
      (count_append__ x (cons head279 tail280))
      (ite
        (=
          x
          head279)
        (+ (count_append__ x tail280) 1)
        (count_append__ x tail280)))))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)))
    (=
      (append_drop |n'| nil zs)
      zs)))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)) (head281 Elem) (tail282 (List Elem)))
    (=
      (append_drop |n'| (cons head281 tail282) zs)
      (ite
        (<= |n'| 0)
        (cons head281 (append tail282 zs))
        (append_drop (- |n'| 1) tail282 zs)))))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)))
    (=
      (append_take |n'| nil zs)
      zs)))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)) (head283 Elem) (tail284 (List Elem)))
    (=
      (append_take |n'| (cons head283 tail284) zs)
      (ite
        (<= |n'| 0)
        zs
        (cons head283 (append_take (- |n'| 1) tail284 zs))))))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)))
    (=
      (append_take__ |n'| nil zs)
      nil)))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)) (head283 Elem) (tail284 (List Elem)))
    (=
      (append_take__ |n'| (cons head283 tail284) zs)
      (ite
        (<= |n'| 0)
        zs
        (cons head283 (append_take__ (- |n'| 1) tail284 zs))))))
(assert
  (forall
    ((|z'| Elem) (zs (List Elem)))
    (=
      (append_snoc nil |z'| zs)
      (cons |z'| zs))))
(assert
  (forall
    ((|z'| Elem) (zs (List Elem)) (head285 Elem) (tail286 (List Elem)))
    (=
      (append_snoc (cons head285 tail286) |z'| zs)
      (cons head285 (append_snoc tail286 |z'| zs)))))
(assert
  (=
    (append_snoc__ nil)
    nil))
(assert
  (forall
    ((head285 Elem) (tail286 (List Elem)))
    (=
      (append_snoc__ (cons head285 tail286))
      (cons head285 (append_snoc__ tail286)))))
(assert
  (forall
    ((|x'| Elem) (zs (List Elem)))
    (=
      (append_remove |x'| nil zs)
      zs)))
(assert
  (forall
    ((|x'| Elem) (zs (List Elem)) (head287 Elem) (tail288 (List Elem)))
    (=
      (append_remove |x'| (cons head287 tail288) zs)
      (ite
        (=
          |x'|
          head287)
        (append_remove |x'| tail288 zs)
        (cons head287 (append_remove |x'| tail288 zs))))))
(assert
  (forall
    ((|x'| Elem))
    (=
      (append_remove__ |x'| nil)
      nil)))
(assert
  (forall
    ((|x'| Elem) (head287 Elem) (tail288 (List Elem)))
    (=
      (append_remove__ |x'| (cons head287 tail288))
      (ite
        (=
          |x'|
          head287)
        (append_remove__ |x'| tail288)
        (cons head287 (append_remove__ |x'| tail288))))))
(assert
  (forall
    ((|zs'| (List Elem)) (zs (List Elem)))
    (=
      (append_reverse-accumulator nil |zs'| zs)
      (append |zs'| zs))))
(assert
  (forall
    ((|zs'| (List Elem)) (zs (List Elem)) (head289 Elem) (tail290 (List Elem)))
    (=
      (append_reverse-accumulator (cons head289 tail290) |zs'| zs)
      (append_reverse-accumulator tail290 (cons head289 |zs'|) zs))))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)))
    (=
      (append_rotate |n'| nil zs)
      zs)))
(assert
  (forall
    ((|n'| Int) (zs (List Elem)) (head291 Elem) (tail292 (List Elem)))
    (=
      (append_rotate |n'| (cons head291 tail292) zs)
      (ite
        (<= |n'| 0)
        (cons head291 (append tail292 zs))
        (append (snoc (rotate (- |n'| 1) tail292) head291) zs)))))
(assert
  (forall
    ((zs (List Elem)))
    (=
      (append_reverse nil zs)
      zs)))
(assert
  (forall
    ((zs (List Elem)) (head293 Elem) (tail294 (List Elem)))
    (=
      (append_reverse (cons head293 tail294) zs)
      (append (reverse tail294) (cons head293 zs)))))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (zs (List Elem)))
    (=
      (append_filter |f'| nil zs)
      zs)))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (zs (List Elem)) (head295 Elem) (tail296 (List Elem)))
    (=
      (append_filter |f'| (cons head295 tail296) zs)
      (ite
        (select |f'| head295)
        (append_filter |f'| tail296 zs)
        (cons head295 (append_filter |f'| tail296 zs))))))
(assert
  (forall
    ((|f'| (Array Elem Bool)))
    (=
      (append_filter__ |f'| nil)
      nil)))
(assert
  (forall
    ((|f'| (Array Elem Bool)) (head295 Elem) (tail296 (List Elem)))
    (=
      (append_filter__ |f'| (cons head295 tail296))
      (ite
        (select |f'| head295)
        (append_filter__ |f'| tail296)
        (cons head295 (append_filter__ |f'| tail296))))))
(assert
  (forall
    ((|f'| (Array Elem Elem)) (zs (List Elem)))
    (=
      (append_map |f'| nil zs)
      zs)))
(assert
  (forall
    ((|f'| (Array Elem Elem)) (zs (List Elem)) (head297 Elem) (tail298 (List Elem)))
    (=
      (append_map |f'| (cons head297 tail298) zs)
      (cons (select |f'| head297) (append_map |f'| tail298 zs)))))
(assert
  (forall
    ((|f'| (Array Elem Elem)))
    (=
      (append_map__ |f'| nil)
      nil)))
(assert
  (forall
    ((|f'| (Array Elem Elem)) (head297 Elem) (tail298 (List Elem)))
    (=
      (append_map__ |f'| (cons head297 tail298))
      (cons (select |f'| head297) (append_map__ |f'| tail298)))))
(assert
  (forall
    ((|zs'| (List Elem)) (zs (List Elem)))
    (=
      (append_append nil |zs'| zs)
      (append |zs'| zs))))
(assert
  (forall
    ((|zs'| (List Elem)) (zs (List Elem)) (head299 Elem) (tail300 (List Elem)))
    (=
      (append_append (cons head299 tail300) |zs'| zs)
      (cons head299 (append_append tail300 |zs'| zs)))))
(assert
  (=
    (append_append__ nil)
    nil))
(assert
  (forall
    ((head299 Elem) (tail300 (List Elem)))
    (=
      (append_append__ (cons head299 tail300))
      (cons head299 (append_append__ tail300)))))
(check-sat)
