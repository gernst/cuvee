# benchmark: evaluation/lemmas/list/map comparison for structural

## lemmas found by structural

### reduced

    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))
    forall x: list :: (append(x, nil) == x)

### implied


### trivial



## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate


### unique over thesy




# benchmark: evaluation/lemmas/list/map comparison for conditional

## lemmas found by conditional

### reduced

    forall x₀: nat, x₁: nat, x₂: list :: (leq(length(x₂), x₁) ==> (take(x₀, drop(x₁, x₂)) == nil))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x₀: nat, x₁: list :: (lt(x₀, length(x₁)) ==> (length(take(x₀, x₁)) == x₀))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: nat, x₁: list :: (lt(x₀, length(x₁)) ==> (leq(x₀, length(x₁)) <==> true))
    forall x₀: list, x₁: nat :: (lt(x₁, length(x₀)) ==> (lt(length(x₀), x₁) <==> false))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))
    forall x₀: nat, x₁: list :: (leq(length(x₁), x₀) ==> (take(x₀, x₁) == x₁))
    forall x: list :: (append(x, nil) == x)

### implied

    forall x₀: nat, x₁: list, x₂: list :: (leq(length(x₁), x₀) ==> (append(drop(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: list :: (leq(length(x₁), x₀) ==> (length(drop(x₀, x₁)) == zero))
    forall x₀: nat, x₁: nat, x₂: list :: (leq(length(x₂), x₁) ==> (drop(x₀, drop(x₁, x₂)) == nil))
    forall x₀: [nat]nat, x₁: nat, x₂: list :: (leq(length(x₂), x₁) ==> (map(x₀, drop(x₁, x₂)) == nil))
    forall x₀: nat, x₁: list :: (leq(length(x₁), x₀) ==> (drop(x₀, x₁) == nil))

### trivial



## unique lemmas found by conditional

### overall unique


### unique over structural


### unique over enumerate


### unique over thesy




# benchmark: evaluation/lemmas/list/map comparison for enumerate

## lemmas found by enumerate

### reduced

    forall x₁: list :: (x₁ == append(x₁, nil))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(drop(zero, y₀), append(y₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: list :: (take(x₀, take(y₀, y₁)) == take(y₀, take(x₀, y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(append(y₀, y₁), drop(zero, x₁)))
    forall y₀: [nat]nat, y₁: list, x₁: list :: (append(map(y₀, y₁), x₁) == append(map(y₀, y₁), drop(zero, x₁)))
    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, drop(y₀, y₁)) == append(drop(zero, x₀), drop(y₀, y₁)))
    forall y₀: nat, y₁: list, x₁: list :: (append(take(y₀, y₁), x₁) == append(take(y₀, y₁), drop(zero, x₁)))
    forall y₀: nat, x₁: nat :: (leq(succ(y₀), x₁) <==> lt(y₀, x₁))
    forall y₀: list, x₁: list :: (drop(length(y₀), x₁) == drop(length(y₀), drop(zero, x₁)))
    forall y₀: list, x₁: list :: (take(length(y₀), x₁) == take(length(y₀), drop(zero, x₁)))
    forall y₀: list, y₁: list :: (append(y₀, y₁) == append(y₀, drop(zero, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: nat, x₁: list :: (take(succ(y₀), x₁) == take(succ(y₀), drop(zero, x₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(drop(zero, y₁)))

### implied


### trivial



## unique lemmas found by enumerate

### overall unique


### unique over structural


### unique over conditional


### unique over thesy




# benchmark: evaluation/lemmas/list/map comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_nat_0: nat :: (lt(?ts_ph_nat_0, ?ts_ph_nat_0) <==> false)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, ?ts_ph_nat_0) <==> true)
    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == append(?ts_ph_list_0, nil))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list :: (length(map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat :: (lt(?ts_ph_nat_0, succ(?ts_ph_nat_0)) <==> true)
    forall ?ts_ph_nat_0: nat :: (leq(succ(?ts_ph_nat_0), ?ts_ph_nat_0) <==> false)
    forall ?ts_ph_nat_0: nat :: (lt(succ(?ts_ph_nat_0), ?ts_ph_nat_0) <==> false)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (lt(?ts_ph_nat_1, length(?ts_ph_list_0)) <==> leq(succ(?ts_ph_nat_1), length(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (leq(length(?ts_ph_list_0), ?ts_ph_nat_1) <==> lt(length(?ts_ph_list_0), succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (drop(length(?ts_ph_list_0), append(?ts_ph_list_0, ?ts_ph_list_1)) == ?ts_ph_list_1)
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (take(length(?ts_ph_list_0), append(?ts_ph_list_0, ?ts_ph_list_1)) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (take(succ(zero), append(?ts_ph_list_0, ?ts_ph_list_0)) == take(succ(zero), ?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(map(?ts_ph_POfn_nat_natPC_0, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_0, ?ts_ph_list_1)) == map(?ts_ph_POfn_nat_natPC_0, append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (lt(?ts_ph_nat_0, ?ts_ph_nat_1) <==> leq(succ(?ts_ph_nat_0), ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, succ(?ts_ph_nat_0)) <==> true)
    forall ?ts_ph_nat_1: nat, ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list :: (drop(?ts_ph_nat_1, map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0)) == map(?ts_ph_POfn_nat_natPC_1, drop(?ts_ph_nat_1, ?ts_ph_list_0)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (map(?ts_ph_POfn_nat_natPC_1, take(?ts_ph_nat_1, ?ts_ph_list_0)) == take(?ts_ph_nat_1, map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (drop(?ts_ph_nat_1, take(?ts_ph_nat_1, ?ts_ph_list_0)) == nil)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (take(?ts_ph_nat_1, take(?ts_ph_nat_1, ?ts_ph_list_0)) == take(?ts_ph_nat_1, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (drop(succ(?ts_ph_nat_1), take(?ts_ph_nat_1, ?ts_ph_list_0)) == nil)

### implied

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == drop(zero, ?ts_ph_list_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (leq(succ(?ts_ph_nat_1), length(?ts_ph_list_0)) <==> lt(?ts_ph_nat_1, length(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (lt(length(?ts_ph_list_0), succ(?ts_ph_nat_1)) <==> leq(length(?ts_ph_list_0), ?ts_ph_nat_1))
    forall ?ts_ph_list_0: list, ?ts_ph_POfn_nat_natPC_1: [nat]nat :: (drop(length(?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0)) == nil)
    forall ?ts_ph_list_0: list, ?ts_ph_POfn_nat_natPC_1: [nat]nat :: (take(length(?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0)) == map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list :: (map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0) == take(length(?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_POfn_nat_natPC_1: [nat]nat :: (drop(length(?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0)) == drop(length(?ts_ph_list_0), ?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (take(succ(zero), ?ts_ph_list_0) == take(succ(zero), append(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (take(length(?ts_ph_list_0), ?ts_ph_list_0) == take(length(?ts_ph_list_0), append(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (take(length(?ts_ph_list_0), append(?ts_ph_list_0, ?ts_ph_list_0)) == take(length(?ts_ph_list_0), ?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (map(?ts_ph_POfn_nat_natPC_0, append(?ts_ph_list_0, ?ts_ph_list_1)) == append(map(?ts_ph_POfn_nat_natPC_0, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(succ(?ts_ph_nat_0), ?ts_ph_nat_1) <==> lt(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (map(?ts_ph_POfn_nat_natPC_1, drop(?ts_ph_nat_1, ?ts_ph_list_0)) == drop(?ts_ph_nat_1, map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list :: (take(?ts_ph_nat_1, map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0)) == map(?ts_ph_POfn_nat_natPC_1, take(?ts_ph_nat_1, ?ts_ph_list_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (take(?ts_ph_nat_1, ?ts_ph_list_0) == take(?ts_ph_nat_1, take(?ts_ph_nat_1, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))

### trivial

    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (take(zero, ?ts_ph_list_0) == nil)
    forall ?ts_ph_nat_0: nat :: (leq(succ(zero), ?ts_ph_nat_0) <==> lt(zero, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (lt(zero, ?ts_ph_nat_0) <==> leq(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (lt(?ts_ph_nat_0, succ(zero)) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> lt(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)))


## unique lemmas found by thesy

### overall unique


### unique over structural


### unique over conditional

    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)))

### unique over enumerate

    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)))



