(declare-var a (Array Int Int))
(declare-var max Int)
(declare-var max1 Int)
(declare-var l Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel inv ((Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv a 0 0 l))

(rule (=> (and (inv a i max l)
        (< i l)
        (= max1 (ite (< max (select a i)) (select a i) max))
        (= i1 (+ i 1)))
    (inv a i1 max1 l)))

(rule (=> (and (inv a i max l)
        (>= i l)
        (not (=>
            (and (<= 0 l)
                (exists ((k Int)) (and (<= 0 k) (< k l) (<= 0 (select a k)))))
                (exists ((k Int)) (and (<= 0 k) (< k l) (= max (select a k)))))))
	  fail))

(query fail)
