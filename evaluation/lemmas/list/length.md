# benchmark: evaluation/lemmas/list/length comparison for structural

## lemmas found by structural

### reduced

    forall y₀: list, y₁: nat, x₁: nat :: (add(nlength(y₀, y₁), x₁) == nlength(y₀, add(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == nlength(y₀, x₁))
    forall x: nat :: (add(x, zero) == x)

### implied


### trivial



## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate


### unique over thesy




# benchmark: evaluation/lemmas/list/length comparison for conditional

## lemmas found by conditional

### reduced

    forall y₀: list, y₁: nat, x₁: nat :: (add(nlength(y₀, y₁), x₁) == nlength(y₀, add(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == nlength(y₀, x₁))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x: list, z₀: nat :: ((zero == z₀) ==> (length(x) == nlength(x, z₀)))

### trivial



## unique lemmas found by conditional

### overall unique


### unique over structural


### unique over enumerate


### unique over thesy




# benchmark: evaluation/lemmas/list/length comparison for enumerate

## lemmas found by enumerate

### reduced

    forall y₀: list :: (length(y₀) == nlength(y₀, zero))
    forall x₀: nat :: (x₀ == add(x₀, zero))
    forall y₀: list, y₁: nat, x₁: nat :: (add(nlength(y₀, y₁), x₁) == add(nlength(y₀, zero), add(y₁, x₁)))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, y₁: nat, x₁: nat :: (add(qlength(y₀, y₁), x₁) == nlength(y₀, add(y₁, x₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: list, y₁: nat, x₁: nat :: (add(nlength(y₀, y₁), x₁) == add(add(x₁, zero), qlength(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall y₁: list, x₁: nat :: (qlength(y₁, succ(x₁)) == nlength(y₁, succ(x₁)))
    forall y₁: list, x₁: nat :: (succ(nlength(y₁, x₁)) == nlength(y₁, succ(x₁)))
    forall x₀: list, y₀: list, y₁: nat :: (nlength(x₀, qlength(y₀, y₁)) == nlength(y₀, qlength(x₀, y₁)))

### implied

    forall x₀: list, y₀: list, y₁: nat :: (nlength(x₀, nlength(y₀, y₁)) == add(qlength(x₀, y₁), length(y₀)))
    forall x₀: list, y₀: list, y₁: nat :: (qlength(x₀, nlength(y₀, y₁)) == add(qlength(y₀, zero), nlength(x₀, y₁)))
    forall x₀: list, y₀: list, y₁: nat :: (qlength(x₀, qlength(y₀, y₁)) == add(nlength(x₀, y₁), length(y₀)))

### trivial



## unique lemmas found by enumerate

### overall unique


### unique over structural


### unique over conditional


### unique over thesy




# benchmark: evaluation/lemmas/list/length comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_list_0: list :: (length(?ts_ph_list_0) == nlength(?ts_ph_list_0, zero))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (succ(nlength(?ts_ph_list_0, ?ts_ph_nat_1)) == nlength(?ts_ph_list_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (qlength(?ts_ph_list_0, succ(?ts_ph_nat_1)) == nlength(?ts_ph_list_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qlength(?ts_ph_list_0, length(?ts_ph_list_1)) == qlength(?ts_ph_list_1, length(?ts_ph_list_0)))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (qlength(?ts_ph_list_1, qlength(?ts_ph_list_0, ?ts_ph_nat_1)) == qlength(?ts_ph_list_0, qlength(?ts_ph_list_1, ?ts_ph_nat_1)))

### implied

    forall ?ts_ph_list_0: list :: (nlength(?ts_ph_list_0, zero) == length(?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (nlength(?ts_ph_list_0, succ(?ts_ph_nat_1)) == succ(nlength(?ts_ph_list_0, ?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (nlength(?ts_ph_list_0, succ(?ts_ph_nat_1)) == qlength(?ts_ph_list_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qlength(?ts_ph_list_0, length(?ts_ph_list_1)) == nlength(?ts_ph_list_0, length(?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (nlength(?ts_ph_list_0, length(?ts_ph_list_1)) == qlength(?ts_ph_list_0, length(?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (succ(qlength(?ts_ph_list_0, ?ts_ph_nat_0)) == succ(nlength(?ts_ph_list_0, ?ts_ph_nat_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (succ(nlength(?ts_ph_list_0, ?ts_ph_nat_0)) == succ(qlength(?ts_ph_list_0, ?ts_ph_nat_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (cons(nlength(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == cons(qlength(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (cons(qlength(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == cons(nlength(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (qlength(?ts_ph_list_1, nlength(?ts_ph_list_0, ?ts_ph_nat_1)) == qlength(?ts_ph_list_1, qlength(?ts_ph_list_0, ?ts_ph_nat_1)))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (qlength(?ts_ph_list_1, qlength(?ts_ph_list_0, ?ts_ph_nat_1)) == qlength(?ts_ph_list_1, nlength(?ts_ph_list_0, ?ts_ph_nat_1)))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (nlength(?ts_ph_list_1, qlength(?ts_ph_list_0, ?ts_ph_nat_0)) == nlength(?ts_ph_list_1, nlength(?ts_ph_list_0, ?ts_ph_nat_0)))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (nlength(?ts_ph_list_1, nlength(?ts_ph_list_0, ?ts_ph_nat_0)) == nlength(?ts_ph_list_1, qlength(?ts_ph_list_0, ?ts_ph_nat_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (qlength(?ts_ph_list_0, nlength(?ts_ph_list_1, ?ts_ph_nat_0)) == nlength(?ts_ph_list_0, nlength(?ts_ph_list_1, ?ts_ph_nat_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (nlength(?ts_ph_list_0, nlength(?ts_ph_list_1, ?ts_ph_nat_0)) == qlength(?ts_ph_list_0, nlength(?ts_ph_list_1, ?ts_ph_nat_0)))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list :: (qlength(?ts_ph_list_1, length(?ts_ph_list_0)) == qlength(?ts_ph_list_0, length(?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_1: nat :: (qlength(?ts_ph_list_0, qlength(?ts_ph_list_1, ?ts_ph_nat_1)) == qlength(?ts_ph_list_1, qlength(?ts_ph_list_0, ?ts_ph_nat_1)))

### trivial



## unique lemmas found by thesy

### overall unique


### unique over structural


### unique over conditional


### unique over enumerate




