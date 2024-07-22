(declare-var a (Array Int Int))
(declare-var v Int)
(declare-var l Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel inv ((Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv a 0 v l))

(rule (=> (and (inv a i v l) (< i l) (not (= (select a i) v)) (= i1 (+ i 1))) (inv a i1 v l)))

(rule (=> (and (inv a i v l) (not (and (< i l) (not (= (select a i) v))))
	       (not (=> (and (<= 0 l) (< i l)) (exists ((pos Int)) (= (select a pos) v)))))
	  fail))

(query fail)
