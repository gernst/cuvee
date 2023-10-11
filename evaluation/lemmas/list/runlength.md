# benchmark: evaluation/lemmas/list/runlength comparison for structural

## lemmas found by structural

### reduced

    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₀), sum(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied


### trivial



## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate

    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))

### unique over thesy

    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₀), sum(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))


## lemmas confirmed by conditional

### reduced

    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₀), sum(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied


### trivial



## lemmas confirmed by enumerate

### reduced

    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₀), sum(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied


### trivial



## lemmas confirmed by thesy

### reduced

    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied


### trivial




# benchmark: evaluation/lemmas/list/runlength comparison for conditional

## lemmas found by conditional

### reduced

    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₀), sum(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied


### trivial



## unique lemmas found by conditional

### overall unique


### unique over structural


### unique over enumerate

    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))

### unique over thesy

    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₀), sum(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))


## lemmas confirmed by structural

### reduced

    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₀), sum(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied


### trivial



## lemmas confirmed by enumerate

### reduced

    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₀), sum(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied


### trivial



## lemmas confirmed by thesy

### reduced

    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied


### trivial




# benchmark: evaluation/lemmas/list/runlength comparison for enumerate

## lemmas found by enumerate

### reduced

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, y₁: list, x₁: nat :: (add(sumruns(y₀, y₁), x₁) == add(sumruns(y₀, y₁), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: list, y₁: list, x₁: nat :: (add(sumruns(y₀, y₁), x₁) == add(x₁, sumruns(y₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀))
    forall y₀: list, y₁: list, x₁: list :: (append(decode(y₀, y₁), x₁) == append(decode(y₀, y₁), append(x₁, nil)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == add(mul(x₀, y₁), mul(x₀, y₀)))
    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₁), sum(y₀)))
    forall x₀: nat, y₀: nat :: (mul(x₀, succ(y₀)) == add(mul(x₀, y₀), x₀))

### implied


### trivial



## unique lemmas found by enumerate

### overall unique

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: list, y₁: list, x₁: nat :: (add(sumruns(y₀, y₁), x₁) == add(x₁, sumruns(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == add(mul(x₀, y₁), mul(x₀, y₀)))
    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₁), sum(y₀)))
    forall x₀: nat, y₀: nat :: (mul(x₀, succ(y₀)) == add(mul(x₀, y₀), x₀))

### unique over structural

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: list, y₁: list, x₁: nat :: (add(sumruns(y₀, y₁), x₁) == add(x₁, sumruns(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == add(mul(x₀, y₁), mul(x₀, y₀)))
    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₁), sum(y₀)))
    forall x₀: nat, y₀: nat :: (mul(x₀, succ(y₀)) == add(mul(x₀, y₀), x₀))

### unique over conditional

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: list, y₁: list, x₁: nat :: (add(sumruns(y₀, y₁), x₁) == add(x₁, sumruns(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == add(mul(x₀, y₁), mul(x₀, y₀)))
    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₁), sum(y₀)))
    forall x₀: nat, y₀: nat :: (mul(x₀, succ(y₀)) == add(mul(x₀, y₀), x₀))

### unique over thesy

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: list, y₁: list, x₁: nat :: (add(sumruns(y₀, y₁), x₁) == add(x₁, sumruns(y₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == add(mul(x₀, y₁), mul(x₀, y₀)))
    forall y₀: list, y₁: list :: (sum(append(y₀, y₁)) == add(sum(y₁), sum(y₀)))
    forall x₀: nat, y₀: nat :: (mul(x₀, succ(y₀)) == add(mul(x₀, y₀), x₀))


## lemmas confirmed by structural

### reduced

    forall y₀: list, y₁: list, x₁: nat :: (add(sumruns(y₀, y₁), x₁) == add(sumruns(y₀, y₁), add(x₁, zero)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: list, y₁: list, x₁: list :: (append(decode(y₀, y₁), x₁) == append(decode(y₀, y₁), append(x₁, nil)))

### implied


### trivial



## lemmas confirmed by conditional

### reduced

    forall y₀: list, y₁: list, x₁: nat :: (add(sumruns(y₀, y₁), x₁) == add(sumruns(y₀, y₁), add(x₁, zero)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: list, y₁: list, x₁: list :: (append(decode(y₀, y₁), x₁) == append(decode(y₀, y₁), append(x₁, nil)))

### implied


### trivial



## lemmas confirmed by thesy

### reduced

    forall y₀: list, y₁: list, x₁: nat :: (add(sumruns(y₀, y₁), x₁) == add(sumruns(y₀, y₁), add(x₁, zero)))
    forall y₀: list, y₁: list, x₁: list :: (append(decode(y₀, y₁), x₁) == append(decode(y₀, y₁), append(x₁, nil)))

### implied


### trivial




# benchmark: evaluation/lemmas/list/runlength comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, ?ts_ph_list_0) <==> true)
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat :: (mul(?ts_ph_nat_0, zero) == zero)

### implied


### trivial

    forall ?ts_ph_list_0: list :: (sumruns(nil, ?ts_ph_list_0) == zero)
    forall ?ts_ph_list_0: list :: (sumruns(?ts_ph_list_0, nil) == zero)
    forall ?ts_ph_list_0: list :: (decode(?ts_ph_list_0, nil) == nil)
    forall ?ts_ph_list_0: list :: (decode(nil, ?ts_ph_list_0) == nil)
    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, nil) <==> is_runs(nil, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (is_runs(nil, ?ts_ph_list_0) <==> is_runs(?ts_ph_list_0, nil))


## unique lemmas found by thesy

### overall unique

    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, ?ts_ph_list_0) <==> true)
    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, nil) <==> is_runs(nil, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (is_runs(nil, ?ts_ph_list_0) <==> is_runs(?ts_ph_list_0, nil))
    forall ?ts_ph_nat_0: nat :: (mul(?ts_ph_nat_0, zero) == zero)

### unique over structural

    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, ?ts_ph_list_0) <==> true)
    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, nil) <==> is_runs(nil, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (is_runs(nil, ?ts_ph_list_0) <==> is_runs(?ts_ph_list_0, nil))
    forall ?ts_ph_nat_0: nat :: (mul(?ts_ph_nat_0, zero) == zero)

### unique over conditional

    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, ?ts_ph_list_0) <==> true)
    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, nil) <==> is_runs(nil, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (is_runs(nil, ?ts_ph_list_0) <==> is_runs(?ts_ph_list_0, nil))
    forall ?ts_ph_nat_0: nat :: (mul(?ts_ph_nat_0, zero) == zero)

### unique over enumerate

    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, ?ts_ph_list_0) <==> true)
    forall ?ts_ph_list_0: list :: (decode(?ts_ph_list_0, nil) == nil)
    forall ?ts_ph_list_0: list :: (is_runs(?ts_ph_list_0, nil) <==> is_runs(nil, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (is_runs(nil, ?ts_ph_list_0) <==> is_runs(?ts_ph_list_0, nil))
    forall ?ts_ph_nat_0: nat :: (mul(?ts_ph_nat_0, zero) == zero)


## lemmas confirmed by structural

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)

### implied


### trivial

    forall ?ts_ph_list_0: list :: (sumruns(nil, ?ts_ph_list_0) == zero)
    forall ?ts_ph_list_0: list :: (sumruns(?ts_ph_list_0, nil) == zero)
    forall ?ts_ph_list_0: list :: (decode(?ts_ph_list_0, nil) == nil)
    forall ?ts_ph_list_0: list :: (decode(nil, ?ts_ph_list_0) == nil)


## lemmas confirmed by conditional

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)

### implied


### trivial

    forall ?ts_ph_list_0: list :: (sumruns(nil, ?ts_ph_list_0) == zero)
    forall ?ts_ph_list_0: list :: (sumruns(?ts_ph_list_0, nil) == zero)
    forall ?ts_ph_list_0: list :: (decode(?ts_ph_list_0, nil) == nil)
    forall ?ts_ph_list_0: list :: (decode(nil, ?ts_ph_list_0) == nil)


## lemmas confirmed by enumerate

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)

### implied


### trivial

    forall ?ts_ph_list_0: list :: (sumruns(nil, ?ts_ph_list_0) == zero)
    forall ?ts_ph_list_0: list :: (sumruns(?ts_ph_list_0, nil) == zero)
    forall ?ts_ph_list_0: list :: (decode(nil, ?ts_ph_list_0) == nil)



