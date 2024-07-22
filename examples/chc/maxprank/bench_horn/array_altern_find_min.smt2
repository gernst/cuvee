(declare-var a (Array Int Int))
(declare-var min Int)
(declare-var min1 Int)
(declare-var l Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel inv ((Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv a 0 0 l))

(rule (=> (and (inv a i min l) (< i l) (= (ite (> min (select a i)) (select a i) min) min1) (= i1 (+ i 1))) (inv a i1 min1 l)))

(rule (=> (and (inv a i min l) (>= i l)
	       (not (=> (exists ((k Int)) (and (<= 0 l) (<= 0 k) (< k l) (<= (select a k) 0)))  (exists ((k Int)) (and (<= 0 k) (< k l) (= min (select a k)))))))
	  fail))

(query fail)
