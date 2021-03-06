(set-logic ALL)
(declare-sort Elem 0)
(declare-datatypes ((Lst 0)) (((cons (head Elem) (tail Lst)) (nil))))
(declare-fun R (Lst Int (Array Int Elem)) Bool)
(push 1)
(push 1)
(assert
  (forall
    ((x Elem) (xs Lst) (m Int) (n Int) (values (Array Int Elem)))
    (=>
      (and
        (<= m n)
        (R xs m values))
      (R xs m (store values n x)))))
(assert
  (forall
    ((head1 Elem) (tail2 Lst) (size Int) (values (Array Int Elem)))
    (=
      (R (cons head1 tail2) size values)
      (and
        (< 0 size)
        (= head1 (select values (- size 1)))
        (R tail2 (- size 1) values)))))
(assert
  (forall
    ((size Int) (values (Array Int Elem)))
    (=
      (R nil size values)
      (= 0 size))))
(assert
  (not
    (and
      (forall
        ((values (Array Int Elem)))
        (=>
          (and
            true
            true
            true)
          (and
            true
            true
            (R nil 0 values))))
      (forall
        ((xs Lst) (x Elem) (size Int) (values (Array Int Elem)) (|x'| Elem))
        (=>
          (and
            (= |x'| x)
            true
            (R xs size values))
          (and
            true
            true
            (R (cons x xs) (+ size 1) (store values size |x'|)))))
      (forall
        ((xs Lst) (size Int) (values (Array Int Elem)))
        (=>
          (and
            true
            (distinct xs nil)
            (R xs size values))
          (and
            (> size 0)
            (= (select values (- size 1)) (head xs))
            (R (tail xs) (- size 1) values)))))))
(check-sat)
(pop 1)
(pop 1)
(push 1)
(push 1)
(assert
  (forall
    ((x Elem) (xs Lst) (m Int) (n Int) (values (Array Int Elem)))
    (=>
      (and
        (<= m n)
        (R xs m values))
      (R xs m (store values n x)))))
(assert
  (forall
    ((head1 Elem) (tail2 Lst) (size Int) (values (Array Int Elem)))
    (=
      (R (cons head1 tail2) size values)
      (and
        (< 0 size)
        (= head1 (select values (- size 1)))
        (R tail2 (- size 1) values)))))
(assert
  (forall
    ((size Int) (values (Array Int Elem)))
    (=
      (R nil size values)
      (= 0 size))))
(assert
  (not
    (and
      (forall
        ((values (Array Int Elem)))
        (=>
          (and
            true
            true
            true)
          (and
            true
            true
            (R nil 0 values))))
      (forall
        ((xs Lst) (x Elem) (size Int) (values (Array Int Elem)) (|x'| Elem))
        (=>
          (and
            (= |x'| x)
            true
            (R xs size values))
          (and
            true
            true
            (R (cons x xs) (+ size 1) (store values size |x'|)))))
      (forall
        ((xs Lst) (size Int) (values (Array Int Elem)))
        (=>
          (and
            true
            (distinct xs nil)
            (R xs size values))
          (and
            (> size 0)
            (= (select values (- size 1)) (head xs))
            (R (tail xs) (- size 1) values)))))))
(check-sat)
(pop 1)
(pop 1)
