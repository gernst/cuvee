(declare-var a (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)

(declare-rel inv ((Array Int Int) Int))
(declare-rel fail ())

(rule (inv a 0))

(rule (=> (and (inv a i) (not (= (select a i) 0)) (= i1 (+ i 1))) (inv a i1)))

(rule (=> (and (inv a i) (= (select a i) 0)
	       (not (=> (exists ((pos Int)) (and (<= 0 pos) (= (select a pos) 0))) (forall ((j Int)) (=> (and (<= 0 j) (< j i)) (not (= (select a j) 0)))))))
	  fail))
(query fail)

