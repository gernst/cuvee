(declare-var a1 (Array Int Int))
(declare-var a2 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var al Int)
(declare-var bl Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var bl1 Int)
(declare-var pos Int)

(declare-rel inv ((Array Int Int) (Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv a1 a2 b 0 al 0))

(rule (=> (and (inv a1 a2 b i al bl) (< i al)
	       (= (ite (= (select a1 i) (select a2 i)) (store b bl i) b) b1)
	       (= (ite (= (select a1 i) (select a2 i)) (+ bl 1) bl) bl1)
	       (= i1 (+ i 1))) (inv a1 a2 b1 i1 al bl1)))

(rule (=> (and (inv a1 a2 b i al bl) (>= i al)
	       (not (forall ((pos Int)) (=> (and (<= 0 al) (<= 0 pos) (< pos al) (= (select a1 pos) (select a2 pos)))
			(exists ((pos2 Int)) (= (select b pos2) pos))))))
	  fail))

(query fail)
