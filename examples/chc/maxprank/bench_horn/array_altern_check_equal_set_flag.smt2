(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var l Int)
(declare-var i Int)
(declare-var r Int)
(declare-var i1 Int)
(declare-var r1 Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

;;property itself is inductive

(rule (inv a b 0 0 l))

(rule (=> (and (inv a b i r l)
    (< i l)
    (= (ite (not (= (select a i) (select b i))) 1 r) r1)
    (= i1 (+ i 1)))
  (inv a b i1 r1 l)))

(rule (=> (and (inv a b i r l) (>= i l)
	       (not (=> (and (<= 0 l) (= r 1)) (exists ((k Int)) (not (= (select a k) (select b k)))))))
	  fail))

(query fail)
