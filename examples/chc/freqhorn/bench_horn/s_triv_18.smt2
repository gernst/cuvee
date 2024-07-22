(declare-rel inv (Bool Int))
(declare-var x Bool)
(declare-var x1 Bool)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (inv false 865655))

(rule (=> 
    (and 
        (inv x y)
        (= y1 (+ (* 248772 y) 1324365726))
    )
    (inv true y1)
  )
)

(rule (=> (and (inv x y) x (not (>= y 216675091386))) fail))

(query fail :print-certificate true)
