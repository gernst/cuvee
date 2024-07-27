(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var c (Array Int Int))
(declare-var c1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var l Int)
(declare-var pos Int)

(declare-rel inv ((Array Int Int) (Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv a b c 0 l))

(rule (=> (and (inv a b c i l)
    (< i l)
    (= c1 (store (store c (* i 2) (select a i)) (+ (* i 2) 1) (select b i)))
    (= i1 (+ i 1)))
  (inv a b c1 i1 l)))

(rule (=> (and (inv a b c i l) (>= i l)
	       (not (forall ((pos Int))
                (exists ((j Int))
                  (=> (and (<= 0 pos) (< pos l))
                      (or (= (select c pos) (select a j))
                          (= (select c pos) (select b j))))))))
	  fail))
(query fail)

	  
