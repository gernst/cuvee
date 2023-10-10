# benchmark: evaluation/lemmas/tree comparison for structural

## lemmas found by structural

### reduced

    forall y₀: tree :: (length(elems(y₀)) == size(y₀))
    forall x₀: [nat]nat, y₀: tree :: (map(x₀, elems(y₀)) == elems(maptree(x₀, y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied

    forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == size(y₁))

### trivial

    forall y₀: tree :: (mirror(mirror(y₀)) == y₀)
    forall y₀: [nat]nat, y₁: tree :: (mirror(maptree(y₀, y₁)) == maptree(y₀, mirror(y₁)))


## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate

    forall y₀: [nat]nat, y₁: tree :: (mirror(maptree(y₀, y₁)) == maptree(y₀, mirror(y₁)))

### unique over thesy




# benchmark: evaluation/lemmas/tree comparison for conditional

## lemmas found by conditional

### reduced

    forall y₀: tree :: (length(elems(y₀)) == size(y₀))
    forall x₀: [nat]nat, y₀: tree :: (map(x₀, elems(y₀)) == elems(maptree(x₀, y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall x: nat :: (add(x, zero) == x)
    forall x: list :: (append(x, nil) == x)

### implied

    forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == size(y₁))

### trivial

    forall y₀: tree :: (mirror(mirror(y₀)) == y₀)
    forall y₀: [nat]nat, y₁: tree :: (mirror(maptree(y₀, y₁)) == maptree(y₀, mirror(y₁)))


## unique lemmas found by conditional

### overall unique


### unique over structural


### unique over enumerate

    forall y₀: [nat]nat, y₁: tree :: (mirror(maptree(y₀, y₁)) == maptree(y₀, mirror(y₁)))

### unique over thesy




# benchmark: evaluation/lemmas/tree comparison for enumerate

## lemmas found by enumerate

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == add(size(y₁), zero))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: tree :: (size(insert(y₀, y₁)) == size(insert(zero, y₁)))
    forall y₀: [nat]nat, y₁: tree :: (elems(maptree(y₀, y₁)) == map(y₀, elems(y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == length(elems(y₁)))
    forall y₀: tree :: (succ(size(y₀)) == size(insert(zero, y₀)))
    forall y₀: tree :: (length(elems(y₀)) == size(y₀))
    forall y₀: tree :: (mirror(mirror(y₀)) == y₀)

### implied

    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(add(y₀, x₀), succ(zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(x₁, y₁), add(y₀, zero)))
    forall y₀: nat :: (succ(y₀) == add(y₀, succ(zero)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₁), length(y₀)))

### trivial



## unique lemmas found by enumerate

### overall unique


### unique over structural


### unique over conditional


### unique over thesy




# benchmark: evaluation/lemmas/tree comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)

### implied


### trivial



## unique lemmas found by thesy

### overall unique


### unique over structural


### unique over conditional


### unique over enumerate




