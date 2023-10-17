# benchmark: evaluation/lemmas/list/rotate comparison for structural

## lemmas found by structural

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x: list :: (append(x, nil) == x)

### trivial



## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate


### unique over thesy

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))


## lemmas confirmed by conditional

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x: list :: (append(x, nil) == x)

### trivial



## lemmas confirmed by enumerate

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x: list :: (append(x, nil) == x)

### trivial



## lemmas confirmed by thesy

### reduced

    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x: list :: (append(x, nil) == x)

### trivial




# benchmark: evaluation/lemmas/list/rotate comparison for conditional

## lemmas found by conditional

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)
    forall x: list, z₀: nat :: (leq(length(x), z₀) ==> (reverse(x) == rotate(z₀, x)))

### implied

    forall x: list :: (append(x, nil) == x)

### trivial



## unique lemmas found by conditional

### overall unique

    forall x: list, z₀: nat :: (leq(length(x), z₀) ==> (reverse(x) == rotate(z₀, x)))

### unique over structural

    forall x: list, z₀: nat :: (leq(length(x), z₀) ==> (reverse(x) == rotate(z₀, x)))

### unique over enumerate

    forall x: list, z₀: nat :: (leq(length(x), z₀) ==> (reverse(x) == rotate(z₀, x)))

### unique over thesy

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall x: list, z₀: nat :: (leq(length(x), z₀) ==> (reverse(x) == rotate(z₀, x)))


## lemmas confirmed by structural

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x: list :: (append(x, nil) == x)

### trivial



## lemmas confirmed by enumerate

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x: list :: (append(x, nil) == x)

### trivial



## lemmas confirmed by thesy

### reduced

    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x: list :: (append(x, nil) == x)

### trivial




# benchmark: evaluation/lemmas/list/rotate comparison for enumerate

## lemmas found by enumerate

### reduced

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, rotate(y₀, y₁)) == append(append(x₀, nil), rotate(y₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), rotate(zero, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: list, x₁: list :: (append(rotate(y₀, y₁), x₁) == append(rotate(y₀, y₁), append(x₁, nil)))
    forall y₀: list :: (length(reverse(y₀)) == length(y₀))
    forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == rotate(length(y₁), cons(y₀, y₁)))
    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == rotate(length(y₀), append(y₀, x₀)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == rotate(zero, rotate(zero, y₀)))

### implied

    forall x₁: list :: (x₁ == append(x₁, nil))

### trivial

    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == append(rotate(zero, x₀), cons(y₀, y₁)))
    forall y₁: list, x₁: list :: (append(y₁, x₁) == append(y₁, rotate(zero, x₁)))
    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == append(rotate(zero, x₀), reverse(y₀)))


## unique lemmas found by enumerate

### overall unique

    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == rotate(length(y₀), append(y₀, x₀)))

### unique over structural

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == append(rotate(zero, x₀), cons(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), rotate(zero, y₁)))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀))
    forall y₁: list, x₁: list :: (append(y₁, x₁) == append(y₁, rotate(zero, x₁)))
    forall y₀: list :: (length(reverse(y₀)) == length(y₀))
    forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == rotate(length(y₁), cons(y₀, y₁)))
    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == rotate(length(y₀), append(y₀, x₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == rotate(zero, rotate(zero, y₀)))

### unique over conditional

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == append(rotate(zero, x₀), cons(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), rotate(zero, y₁)))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀))
    forall y₁: list, x₁: list :: (append(y₁, x₁) == append(y₁, rotate(zero, x₁)))
    forall y₀: list :: (length(reverse(y₀)) == length(y₀))
    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == append(rotate(zero, x₀), reverse(y₀)))
    forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == rotate(length(y₁), cons(y₀, y₁)))
    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == rotate(length(y₀), append(y₀, x₀)))

### unique over thesy

    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == rotate(length(y₀), append(y₀, x₀)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == rotate(zero, rotate(zero, y₀)))


## lemmas confirmed by structural

### reduced

    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, rotate(y₀, y₁)) == append(append(x₀, nil), rotate(y₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: list, x₁: list :: (append(rotate(y₀, y₁), x₁) == append(rotate(y₀, y₁), append(x₁, nil)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))

### implied

    forall x₁: list :: (x₁ == append(x₁, nil))

### trivial

    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == append(rotate(zero, x₀), reverse(y₀)))


## lemmas confirmed by conditional

### reduced

    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, rotate(y₀, y₁)) == append(append(x₀, nil), rotate(y₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: list, x₁: list :: (append(rotate(y₀, y₁), x₁) == append(rotate(y₀, y₁), append(x₁, nil)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == rotate(zero, rotate(zero, y₀)))

### implied

    forall x₁: list :: (x₁ == append(x₁, nil))

### trivial



## lemmas confirmed by thesy

### reduced

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, rotate(y₀, y₁)) == append(append(x₀, nil), rotate(y₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, y₀))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: list, x₁: list :: (append(rotate(y₀, y₁), x₁) == append(rotate(y₀, y₁), append(x₁, nil)))
    forall y₀: list :: (length(reverse(y₀)) == length(y₀))
    forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == rotate(length(y₁), cons(y₀, y₁)))

### implied

    forall x₁: list :: (x₁ == append(x₁, nil))

### trivial

    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == append(rotate(zero, x₀), cons(y₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), rotate(zero, y₁)))
    forall y₁: list, x₁: list :: (append(y₁, x₁) == append(y₁, rotate(zero, x₁)))
    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == append(rotate(zero, x₀), reverse(y₀)))



# benchmark: evaluation/lemmas/list/rotate comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, ?ts_ph_nat_0) <==> true)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, succ(?ts_ph_nat_0)) <==> true)
    forall ?ts_ph_nat_0: nat :: (succ(?ts_ph_nat_0) == add(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(succ(zero), ?ts_ph_nat_1))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (rotate(length(?ts_ph_list_0), cons(?ts_ph_nat_0, ?ts_ph_list_0)) == reverse(cons(?ts_ph_nat_0, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_list_0: list :: (length(reverse(?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (length(rotate(?ts_ph_nat_1, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (reverse(?ts_ph_list_0) == rotate(length(?ts_ph_list_0), ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) <==> leq(?ts_ph_nat_1, zero))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), succ(?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, succ(zero)))

### implied

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, succ(zero)) == succ(?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_0: list :: (reverse(cons(?ts_ph_nat_0, ?ts_ph_list_0)) == rotate(length(?ts_ph_list_0), cons(?ts_ph_nat_0, ?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_list_0: list :: (length(?ts_ph_list_0) == length(reverse(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (rotate(length(?ts_ph_list_0), ?ts_ph_list_0) == reverse(?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))

### trivial

    forall ?ts_ph_list_0: list :: (rotate(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (rotate(?ts_ph_nat_0, cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, nil))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(zero)) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(zero)))
    forall ?ts_ph_nat_0: nat :: (leq(succ(zero), ?ts_ph_nat_0) <==> leq(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (leq(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)) <==> leq(succ(zero), ?ts_ph_nat_0))


## unique lemmas found by thesy

### overall unique

    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, ?ts_ph_nat_0) <==> true)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, succ(?ts_ph_nat_0)) <==> true)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(succ(zero), ?ts_ph_nat_1))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (length(rotate(?ts_ph_nat_1, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) <==> leq(?ts_ph_nat_1, zero))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), succ(?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, succ(zero)))

### unique over structural

    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, ?ts_ph_nat_0) <==> true)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, succ(?ts_ph_nat_0)) <==> true)
    forall ?ts_ph_nat_0: nat :: (succ(?ts_ph_nat_0) == add(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, succ(zero)) == succ(?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(succ(zero), ?ts_ph_nat_1))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (rotate(length(?ts_ph_list_0), cons(?ts_ph_nat_0, ?ts_ph_list_0)) == reverse(cons(?ts_ph_nat_0, ?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_0: list :: (reverse(cons(?ts_ph_nat_0, ?ts_ph_list_0)) == rotate(length(?ts_ph_list_0), cons(?ts_ph_nat_0, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_list_0: list :: (length(reverse(?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (length(?ts_ph_list_0) == length(reverse(?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (length(rotate(?ts_ph_nat_1, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (reverse(?ts_ph_list_0) == rotate(length(?ts_ph_list_0), ?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (rotate(length(?ts_ph_list_0), ?ts_ph_list_0) == reverse(?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) <==> leq(?ts_ph_nat_1, zero))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), succ(?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, succ(zero)))

### unique over conditional

    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, ?ts_ph_nat_0) <==> true)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, succ(?ts_ph_nat_0)) <==> true)
    forall ?ts_ph_nat_0: nat :: (succ(?ts_ph_nat_0) == add(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, succ(zero)) == succ(?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(succ(zero), ?ts_ph_nat_1))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (rotate(length(?ts_ph_list_0), cons(?ts_ph_nat_0, ?ts_ph_list_0)) == reverse(cons(?ts_ph_nat_0, ?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_0: list :: (reverse(cons(?ts_ph_nat_0, ?ts_ph_list_0)) == rotate(length(?ts_ph_list_0), cons(?ts_ph_nat_0, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_list_0: list :: (length(reverse(?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (length(?ts_ph_list_0) == length(reverse(?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (length(rotate(?ts_ph_nat_1, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (reverse(?ts_ph_list_0) == rotate(length(?ts_ph_list_0), ?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (rotate(length(?ts_ph_list_0), ?ts_ph_list_0) == reverse(?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) <==> leq(?ts_ph_nat_1, zero))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), succ(?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, succ(zero)))

### unique over enumerate

    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, ?ts_ph_nat_0) <==> true)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, succ(?ts_ph_nat_0)) <==> true)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (rotate(?ts_ph_nat_0, cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, nil))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(succ(?ts_ph_nat_0), add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> leq(succ(zero), ?ts_ph_nat_1))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (length(rotate(?ts_ph_nat_1, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) <==> leq(?ts_ph_nat_1, zero))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_1), succ(?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, succ(zero)))


## lemmas confirmed by structural

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))

### implied

    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))

### trivial

    forall ?ts_ph_list_0: list :: (rotate(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (rotate(?ts_ph_nat_0, cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, nil))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(zero)) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(zero)))
    forall ?ts_ph_nat_0: nat :: (leq(succ(zero), ?ts_ph_nat_0) <==> leq(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (leq(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)) <==> leq(succ(zero), ?ts_ph_nat_0))


## lemmas confirmed by conditional

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))

### implied

    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))

### trivial

    forall ?ts_ph_list_0: list :: (rotate(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (rotate(?ts_ph_nat_0, cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, nil))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(zero)) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(zero)))
    forall ?ts_ph_nat_0: nat :: (leq(succ(zero), ?ts_ph_nat_0) <==> leq(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (leq(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)) <==> leq(succ(zero), ?ts_ph_nat_0))


## lemmas confirmed by enumerate

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat :: (succ(?ts_ph_nat_0) == add(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (rotate(length(?ts_ph_list_0), cons(?ts_ph_nat_0, ?ts_ph_list_0)) == reverse(cons(?ts_ph_nat_0, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_list_0: list :: (length(reverse(?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))

### implied

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, succ(zero)) == succ(?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_0: list :: (reverse(cons(?ts_ph_nat_0, ?ts_ph_list_0)) == rotate(length(?ts_ph_list_0), cons(?ts_ph_nat_0, ?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_list_0: list :: (length(?ts_ph_list_0) == length(reverse(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))

### trivial

    forall ?ts_ph_list_0: list :: (rotate(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(zero)) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), succ(zero)))
    forall ?ts_ph_nat_0: nat :: (leq(succ(zero), ?ts_ph_nat_0) <==> leq(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (leq(succ(zero), add(?ts_ph_nat_0, ?ts_ph_nat_0)) <==> leq(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_list_0: list :: (reverse(?ts_ph_list_0) == rotate(length(?ts_ph_list_0), ?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (rotate(length(?ts_ph_list_0), ?ts_ph_list_0) == reverse(?ts_ph_list_0))



