(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var m Int)
(declare-var m1 Int)
(declare-var al Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv a b 0 0 al))

(rule (=> (and (inv a b i m al) (< i al)
	       (= (ite (< (select a m) (select a i)) (store b i (select a i)) (store b i (select a m))) b1)
	       (= (ite (< (select a m) (select a i)) i m) m1)
	       (= i1 (+ i 1))) (inv a b1 i1 m1 al)))

(rule (=> (and (inv a b i m al) (>= i al)
	       (not (forall ((j Int)) (exists ((k Int)) (=> (and (<= 0 al) (<= 0 j) (< j al)) (and (<= 0 k) (<= k j) (= (select b j) (select a k))))))))
	  fail))

(query fail)
