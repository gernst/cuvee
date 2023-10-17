# benchmark: evaluation/lemmas/list/remove comparison for structural

## lemmas found by structural

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate


### unique over thesy

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))


## lemmas confirmed by conditional

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## lemmas confirmed by enumerate

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## lemmas confirmed by thesy

### reduced

    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)



# benchmark: evaluation/lemmas/list/remove comparison for conditional

## lemmas found by conditional

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))
    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## unique lemmas found by conditional

### overall unique

    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))

### unique over structural

    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))

### unique over enumerate

    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))

### unique over thesy

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))


## lemmas confirmed by structural

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## lemmas confirmed by enumerate

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## lemmas confirmed by thesy

### reduced

    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)



# benchmark: evaluation/lemmas/list/remove comparison for enumerate

## lemmas found by enumerate

### reduced

    forall x₀: nat :: (x₀ == add(x₀, zero))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(sub(y₀, y₁), x₁) == add(x₁, sub(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall x₀: nat, y₀: nat :: (sub(x₀, succ(y₀)) == sub(sub(x₀, y₀), succ(zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, add(y₀, y₁)) == sub(sub(x₀, y₀), add(y₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(sub(y₀, y₁), x₁) == sub(y₀, add(y₁, x₁)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### implied

    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁))

### trivial



## unique lemmas found by enumerate

### overall unique

    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall x₀: nat, y₀: nat :: (sub(x₀, succ(y₀)) == sub(sub(x₀, y₀), succ(zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, add(y₀, y₁)) == sub(sub(x₀, y₀), add(y₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(sub(y₀, y₁), x₁) == sub(y₀, add(y₁, x₁)))

### unique over structural

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(sub(y₀, y₁), x₁) == add(x₁, sub(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall x₀: nat, y₀: nat :: (sub(x₀, succ(y₀)) == sub(sub(x₀, y₀), succ(zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, add(y₀, y₁)) == sub(sub(x₀, y₀), add(y₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(sub(y₀, y₁), x₁) == sub(y₀, add(y₁, x₁)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### unique over conditional

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(sub(y₀, y₁), x₁) == add(x₁, sub(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall x₀: nat, y₀: nat :: (sub(x₀, succ(y₀)) == sub(sub(x₀, y₀), succ(zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, add(y₀, y₁)) == sub(sub(x₀, y₀), add(y₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(sub(y₀, y₁), x₁) == sub(y₀, add(y₁, x₁)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### unique over thesy

    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall x₀: nat, y₀: nat :: (sub(x₀, succ(y₀)) == sub(sub(x₀, y₀), succ(zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, add(y₀, y₁)) == sub(sub(x₀, y₀), add(y₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(sub(y₀, y₁), x₁) == sub(y₀, add(y₁, x₁)))


## lemmas confirmed by structural

### reduced

    forall x₀: nat :: (x₀ == add(x₀, zero))

### implied

    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁))

### trivial



## lemmas confirmed by conditional

### reduced

    forall x₀: nat :: (x₀ == add(x₀, zero))

### implied

    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁))

### trivial



## lemmas confirmed by thesy

### reduced

    forall x₀: nat :: (x₀ == add(x₀, zero))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(sub(y₀, y₁), x₁) == add(x₁, sub(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### implied


### trivial




# benchmark: evaluation/lemmas/list/remove comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, ?ts_ph_nat_0) == sub(zero, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == zero)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == ?ts_ph_nat_1)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == zero)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_0)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_1, ?ts_ph_nat_0) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (count(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == zero)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) <==> false)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, ?ts_ph_list_0) == remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)))

### implied

    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == sub(?ts_ph_nat_0, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_1) == add(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)) == sub(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(zero)) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == remove(?ts_ph_nat_1, ?ts_ph_list_0))

### trivial

    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == zero)
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == sub(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == count(zero, cons(?ts_ph_nat_0, nil)))
    forall ?ts_ph_nat_0: nat :: (count(zero, cons(?ts_ph_nat_0, nil)) == sub(succ(zero), ?ts_ph_nat_0))


## unique lemmas found by thesy

### overall unique

    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, ?ts_ph_nat_0) == sub(zero, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == sub(?ts_ph_nat_0, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == zero)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == ?ts_ph_nat_1)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == zero)
    forall ?ts_ph_nat_0: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)) == sub(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(zero)) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_1, ?ts_ph_nat_0) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (count(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == zero)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) <==> false)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, ?ts_ph_list_0) == remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == remove(?ts_ph_nat_1, ?ts_ph_list_0))

### unique over structural

    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, ?ts_ph_nat_0) == sub(zero, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == sub(?ts_ph_nat_0, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == zero)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == ?ts_ph_nat_1)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == zero)
    forall ?ts_ph_nat_0: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)) == sub(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(zero)) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_1, ?ts_ph_nat_0) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (count(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == zero)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) <==> false)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, ?ts_ph_list_0) == remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == remove(?ts_ph_nat_1, ?ts_ph_list_0))

### unique over conditional

    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, ?ts_ph_nat_0) == sub(zero, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == sub(?ts_ph_nat_0, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == zero)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == ?ts_ph_nat_1)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == zero)
    forall ?ts_ph_nat_0: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)) == sub(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(zero)) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_1, ?ts_ph_nat_0) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (count(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == zero)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) <==> false)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, ?ts_ph_list_0) == remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == remove(?ts_ph_nat_1, ?ts_ph_list_0))

### unique over enumerate

    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, ?ts_ph_nat_0) == sub(zero, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == sub(?ts_ph_nat_0, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == zero)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == ?ts_ph_nat_1)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == zero)
    forall ?ts_ph_nat_0: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)) == sub(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, succ(zero)) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == sub(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == sub(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_1, ?ts_ph_nat_0) == sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(add(?ts_ph_nat_0, ?ts_ph_nat_1), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (count(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == zero)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) <==> false)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, ?ts_ph_list_0) == remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, remove(?ts_ph_nat_1, ?ts_ph_list_0)) == remove(?ts_ph_nat_1, ?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == count(zero, cons(?ts_ph_nat_0, nil)))
    forall ?ts_ph_nat_0: nat :: (count(zero, cons(?ts_ph_nat_0, nil)) == sub(succ(zero), ?ts_ph_nat_0))


## lemmas confirmed by structural

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_0)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0))

### implied

    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_1) == add(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_0)))

### trivial

    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == zero)
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == sub(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == count(zero, cons(?ts_ph_nat_0, nil)))
    forall ?ts_ph_nat_0: nat :: (count(zero, cons(?ts_ph_nat_0, nil)) == sub(succ(zero), ?ts_ph_nat_0))


## lemmas confirmed by conditional

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_0)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0))

### implied

    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_1) == add(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_0)))

### trivial

    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == zero)
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)) == sub(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == sub(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (sub(succ(zero), ?ts_ph_nat_0) == count(zero, cons(?ts_ph_nat_0, nil)))
    forall ?ts_ph_nat_0: nat :: (count(zero, cons(?ts_ph_nat_0, nil)) == sub(succ(zero), ?ts_ph_nat_0))


## lemmas confirmed by enumerate

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_0)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))

### implied

    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_1) == add(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))

### trivial

    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == zero)



