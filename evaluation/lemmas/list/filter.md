# benchmark: evaluation/lemmas/list/filter comparison for structural

## lemmas found by structural

### reduced

    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate


### unique over thesy




# benchmark: evaluation/lemmas/list/filter comparison for conditional

## lemmas found by conditional

### reduced

    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, x₁) == nil))
    forall x₀: [nat]Bool, x₁: list :: (all(x₀, x₁) ==> (filter(x₀, x₁) == x₁))

### implied

    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, x₁) == zero))
    forall x: list, y₀: [nat]Bool :: (all(y₀, x) ==> (countif(y₀, x) == length(x)))

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## unique lemmas found by conditional

### overall unique


### unique over structural


### unique over enumerate


### unique over thesy




# benchmark: evaluation/lemmas/list/filter comparison for enumerate

## lemmas found by enumerate

### reduced

    forall x₀: [nat]Bool, y₀: [nat]Bool, y₁: list :: (ex(x₀, filter(y₀, y₁)) <==> ex(y₀, filter(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: [nat]Bool, y₁: list :: (filter(x₀, filter(y₀, y₁)) == filter(y₀, filter(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: [nat]Bool, y₁: list :: (countif(x₀, filter(y₀, y₁)) == countif(y₀, filter(x₀, y₁)))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, filter(y₀, y₁)))

### implied


### trivial



## unique lemmas found by enumerate

### overall unique


### unique over structural


### unique over conditional


### unique over thesy




# benchmark: evaluation/lemmas/list/filter comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_POfn_nat_BoolPC_1: [nat]Bool, ?ts_ph_list_0: list :: (countif(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0) == length(filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0)))
    forall ?ts_ph_POfn_nat_BoolPC_1: [nat]Bool, ?ts_ph_list_0: list :: (all(?ts_ph_POfn_nat_BoolPC_1, filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0)) <==> true)
    forall ?ts_ph_POfn_nat_BoolPC_1: [nat]Bool, ?ts_ph_list_0: list :: (countif(?ts_ph_POfn_nat_BoolPC_1, filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0)) == countif(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_BoolPC_1: [nat]Bool, ?ts_ph_list_0: list :: (ex(?ts_ph_POfn_nat_BoolPC_1, filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0)) <==> ex(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_BoolPC_1: [nat]Bool, ?ts_ph_list_0: list :: (filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0) == filter(?ts_ph_POfn_nat_BoolPC_1, filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0)))

### implied

    forall ?ts_ph_POfn_nat_BoolPC_1: [nat]Bool, ?ts_ph_list_0: list :: (length(filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0)) == countif(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_BoolPC_1: [nat]Bool, ?ts_ph_list_0: list :: (countif(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0) == countif(?ts_ph_POfn_nat_BoolPC_1, filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0)))
    forall ?ts_ph_POfn_nat_BoolPC_1: [nat]Bool, ?ts_ph_list_0: list :: (ex(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0) <==> ex(?ts_ph_POfn_nat_BoolPC_1, filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0)))
    forall ?ts_ph_POfn_nat_BoolPC_1: [nat]Bool, ?ts_ph_list_0: list :: (filter(?ts_ph_POfn_nat_BoolPC_1, filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0)) == filter(?ts_ph_POfn_nat_BoolPC_1, ?ts_ph_list_0))

### trivial



## unique lemmas found by thesy

### overall unique


### unique over structural


### unique over conditional


### unique over enumerate




