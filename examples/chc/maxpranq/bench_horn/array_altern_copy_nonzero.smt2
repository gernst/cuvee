(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var b (Array Int Int))
(declare-var al Int)
(declare-var bl Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var al1 Int)
(declare-var k Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv a b 0 0 bl))

(rule (=> (and (inv a b i al bl) (< i bl)
	       (= (ite (= (select b i) 0) a (store a al (select b i))) a1)
	       (= (ite (= (select b i) 0) al (+ al 1)) al1)
	       (= i1 (+ i 1))) (inv a1 b i1 al1 bl)))

(rule (=> (and (inv a b i al bl) (>= i bl)
	       (not (forall ((k Int)) (exists ((l Int)) (=> (and (<= 0 k) (<= 0 bl) (< k al)) (= (select a k) (select b l)))))))
	  fail))

(query fail)
