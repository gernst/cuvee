(declare-var a (Array Int Int))
(declare-var max Int)
(declare-var max1 Int)
(declare-var l Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel inv ((Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv a 1 (select a 0) l))

(rule (=> (and (inv a i max l) (< i l) (= (ite (< max (select a i)) (select a i) max) max1) (= i1 (+ i 1))) (inv a i1 max1 l)))

;modified property from (<= 0 l) to (< 0 l) as former is not safe (ex: l = 0) 
(rule (=> (and (inv a i max l) (>= i l)
	       (not (=> (< 0 l) (exists ((k Int)) (and (<= 0 k) (< k l) (= (select a k) max))))))
	  fail))

(query fail)
