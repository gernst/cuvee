(declare-fun not_ (Bool) Bool)
(assert
  (= (not_ false) true))
(assert
  (= (not_ true) false))
(declare-fun and_ (Bool Bool) Bool)
(assert
  (forall
    ((q Bool))
    (= (and_ false q) false)))
(assert
  (forall ((q Bool)) (= (and_ true q) q)))
(declare-fun or_ (Bool Bool) Bool)
(assert
  (forall ((q Bool)) (= (or_ false q) q)))
(assert
  (forall
    ((q Bool))
    (= (or_ true q) true)))
(declare-fun ite_ (Bool Bool Bool) Bool)
(assert
  (forall
    ((q Bool) (r Bool))
    (= (ite_ false q r) r)))
(assert
  (forall
    ((q Bool) (r Bool))
    (= (ite_ true q r) q)))
