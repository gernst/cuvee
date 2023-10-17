# benchmark: evaluation/lemmas/list comparison for structural

## lemmas found by structural

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall x₀: [nat]nat, y₀: list :: (map(x₀, reverse(y₀)) == reverse(map(x₀, y₀)))
    forall x₀: [nat]nat, y₀: nat, y₁: list :: (map(x₀, rotate(y₀, y₁)) == rotate(y₀, map(x₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: list :: (remove(x₀, append(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (remove(x₀, snoc(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, cons(y₁, nil))))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (filter(x₀, append(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (filter(x₀, snoc(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (countif(x₀, append(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (countif(x₀, snoc(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, cons(y₁, nil))))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat :: (reverse(snoc(y₀, y₁)) == cons(y₁, reverse(y₀)))
    forall x₀: [nat]nat, y₀: list, y₁: nat :: (map(x₀, snoc(y₀, y₁)) == append(map(x₀, y₀), cons(x₀[y₁], nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(take(y₀, y₁), x₁) == append(take(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: [nat]nat, y₁: list, x₁: nat :: (snoc(map(y₀, y₁), x₁) == append(map(y₀, y₁), cons(x₁, nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(remove(y₀, y₁), x₁) == append(remove(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall y₀: [nat]Bool, y₁: list, x₁: nat :: (snoc(filter(y₀, y₁), x₁) == append(filter(y₀, y₁), cons(x₁, nil)))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate

    forall x₀: [nat]nat, y₀: list :: (map(x₀, reverse(y₀)) == reverse(map(x₀, y₀)))
    forall x₀: [nat]nat, y₀: nat, y₁: list :: (map(x₀, rotate(y₀, y₁)) == rotate(y₀, map(x₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: nat :: (map(x₀, snoc(y₀, y₁)) == append(map(x₀, y₀), cons(x₀[y₁], nil)))
    forall x₀: nat, y₀: list, y₁: list :: (remove(x₀, append(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (remove(x₀, snoc(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, cons(y₁, nil))))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(take(y₀, y₁), x₁) == append(take(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: [nat]nat, y₁: list, x₁: nat :: (snoc(map(y₀, y₁), x₁) == append(map(y₀, y₁), cons(x₁, nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(remove(y₀, y₁), x₁) == append(remove(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall y₀: [nat]Bool, y₁: list, x₁: nat :: (snoc(filter(y₀, y₁), x₁) == append(filter(y₀, y₁), cons(x₁, nil)))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (filter(x₀, append(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (filter(x₀, snoc(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (countif(x₀, append(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (countif(x₀, snoc(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, cons(y₁, nil))))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))

### unique over thesy

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall x₀: [nat]nat, y₀: list :: (map(x₀, reverse(y₀)) == reverse(map(x₀, y₀)))
    forall x₀: [nat]nat, y₀: nat, y₁: list :: (map(x₀, rotate(y₀, y₁)) == rotate(y₀, map(x₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: nat :: (map(x₀, snoc(y₀, y₁)) == append(map(x₀, y₀), cons(x₀[y₁], nil)))
    forall x₀: nat, y₀: list, y₁: list :: (remove(x₀, append(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (remove(x₀, snoc(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, cons(y₁, nil))))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (filter(x₀, append(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (filter(x₀, snoc(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (countif(x₀, append(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (countif(x₀, snoc(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, cons(y₁, nil))))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))


## lemmas confirmed by conditional

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall x₀: [nat]nat, y₀: list :: (map(x₀, reverse(y₀)) == reverse(map(x₀, y₀)))
    forall x₀: [nat]nat, y₀: nat, y₁: list :: (map(x₀, rotate(y₀, y₁)) == rotate(y₀, map(x₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: list :: (remove(x₀, append(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (remove(x₀, snoc(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, cons(y₁, nil))))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (filter(x₀, append(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (filter(x₀, snoc(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (countif(x₀, append(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (countif(x₀, snoc(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, cons(y₁, nil))))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat :: (reverse(snoc(y₀, y₁)) == cons(y₁, reverse(y₀)))
    forall x₀: [nat]nat, y₀: list, y₁: nat :: (map(x₀, snoc(y₀, y₁)) == append(map(x₀, y₀), cons(x₀[y₁], nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(take(y₀, y₁), x₁) == append(take(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: [nat]nat, y₁: list, x₁: nat :: (snoc(map(y₀, y₁), x₁) == append(map(y₀, y₁), cons(x₁, nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(remove(y₀, y₁), x₁) == append(remove(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall y₀: [nat]Bool, y₁: list, x₁: nat :: (snoc(filter(y₀, y₁), x₁) == append(filter(y₀, y₁), cons(x₁, nil)))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## lemmas confirmed by enumerate

### reduced

    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat :: (reverse(snoc(y₀, y₁)) == cons(y₁, reverse(y₀)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)


## lemmas confirmed by thesy

### reduced

    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat :: (reverse(snoc(y₀, y₁)) == cons(y₁, reverse(y₀)))
    forall y₀: [nat]Bool, y₁: list, x₁: nat :: (snoc(filter(y₀, y₁), x₁) == append(filter(y₀, y₁), cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall y₀: nat, y₁: list, x₁: nat :: (snoc(take(y₀, y₁), x₁) == append(take(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: [nat]nat, y₁: list, x₁: nat :: (snoc(map(y₀, y₁), x₁) == append(map(y₀, y₁), cons(x₁, nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(remove(y₀, y₁), x₁) == append(remove(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))



# benchmark: evaluation/lemmas/list comparison for conditional

## lemmas found by conditional

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall x₀: [nat]nat, y₀: list :: (map(x₀, reverse(y₀)) == reverse(map(x₀, y₀)))
    forall x₀: [nat]nat, y₀: nat, y₁: list :: (map(x₀, rotate(y₀, y₁)) == rotate(y₀, map(x₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, x₁: list, x₂: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, append(x₁, x₂)) == count(x₀, x₂)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (count(x₀, snoc(x₁, x₂)) == count(x₀, cons(x₂, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (append(filter(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (reverse(filter(x₀, x₁)) == nil))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: list :: (remove(x₀, append(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (remove(x₀, snoc(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, cons(y₁, nil))))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (add(countif(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (filter(x₀, append(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (filter(x₀, snoc(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (countif(x₀, append(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (countif(x₀, snoc(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, cons(y₁, nil))))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: [nat]Bool, x₁: list :: (all(x₀, x₁) ==> (filter(x₀, x₁) == x₁))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat :: (reverse(snoc(y₀, y₁)) == cons(y₁, reverse(y₀)))
    forall x₀: [nat]nat, y₀: list, y₁: nat :: (map(x₀, snoc(y₀, y₁)) == append(map(x₀, y₀), cons(x₀[y₁], nil)))
    forall x₀: [nat]nat, x₁: [nat]Bool, x₂: list :: (not_(ex(x₁, x₂)) ==> (map(x₀, filter(x₁, x₂)) == nil))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(take(y₀, y₁), x₁) == append(take(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: [nat]nat, y₁: list, x₁: nat :: (snoc(map(y₀, y₁), x₁) == append(map(y₀, y₁), cons(x₁, nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(remove(y₀, y₁), x₁) == append(remove(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall y₀: [nat]Bool, y₁: list, x₁: nat :: (snoc(filter(y₀, y₁), x₁) == append(filter(y₀, y₁), cons(x₁, nil)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (snoc(filter(x₀, x₁), x₂) == cons(x₂, nil)))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, append(x₁, x₂)) == filter(x₀, x₂)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (filter(x₀, snoc(x₁, x₂)) == filter(x₀, cons(x₂, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, append(x₁, x₂)) == countif(x₀, x₂)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (countif(x₀, snoc(x₁, x₂)) == countif(x₀, cons(x₂, nil))))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, x₁) == nil))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, x₁) == zero))
    forall x: list :: (append(x, nil) == x)
    forall x: list, y₀: [nat]Bool :: (all(y₀, x) ==> (countif(y₀, x) == length(x)))

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: list, y₀: list, z₀: nat :: ((y₀ == cons(z₀, nil)) ==> (append(x, y₀) == append(x, cons(z₀, nil))))


## unique lemmas found by conditional

### overall unique

    forall x₀: nat, x₁: list, x₂: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, append(x₁, x₂)) == count(x₀, x₂)))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (count(x₀, snoc(x₁, x₂)) == count(x₀, cons(x₂, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (append(filter(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (reverse(filter(x₀, x₁)) == nil))
    forall x₀: [nat]nat, x₁: [nat]Bool, x₂: list :: (not_(ex(x₁, x₂)) ==> (map(x₀, filter(x₁, x₂)) == nil))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (snoc(filter(x₀, x₁), x₂) == cons(x₂, nil)))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (add(countif(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, append(x₁, x₂)) == filter(x₀, x₂)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (filter(x₀, snoc(x₁, x₂)) == filter(x₀, cons(x₂, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, append(x₁, x₂)) == countif(x₀, x₂)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (countif(x₀, snoc(x₁, x₂)) == countif(x₀, cons(x₂, nil))))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, x₁) == nil))
    forall x₀: [nat]Bool, x₁: list :: (all(x₀, x₁) ==> (filter(x₀, x₁) == x₁))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, x₁) == zero))
    forall x: list, y₀: [nat]Bool :: (all(y₀, x) ==> (countif(y₀, x) == length(x)))

### unique over structural

    forall x₀: nat, x₁: list, x₂: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, append(x₁, x₂)) == count(x₀, x₂)))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (count(x₀, snoc(x₁, x₂)) == count(x₀, cons(x₂, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (append(filter(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (reverse(filter(x₀, x₁)) == nil))
    forall x₀: [nat]nat, x₁: [nat]Bool, x₂: list :: (not_(ex(x₁, x₂)) ==> (map(x₀, filter(x₁, x₂)) == nil))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (snoc(filter(x₀, x₁), x₂) == cons(x₂, nil)))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (add(countif(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, append(x₁, x₂)) == filter(x₀, x₂)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (filter(x₀, snoc(x₁, x₂)) == filter(x₀, cons(x₂, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, append(x₁, x₂)) == countif(x₀, x₂)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (countif(x₀, snoc(x₁, x₂)) == countif(x₀, cons(x₂, nil))))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, x₁) == nil))
    forall x₀: [nat]Bool, x₁: list :: (all(x₀, x₁) ==> (filter(x₀, x₁) == x₁))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, x₁) == zero))
    forall x: list, y₀: [nat]Bool :: (all(y₀, x) ==> (countif(y₀, x) == length(x)))

### unique over enumerate

    forall x₀: [nat]nat, y₀: list :: (map(x₀, reverse(y₀)) == reverse(map(x₀, y₀)))
    forall x₀: [nat]nat, y₀: nat, y₁: list :: (map(x₀, rotate(y₀, y₁)) == rotate(y₀, map(x₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, x₁: list, x₂: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, append(x₁, x₂)) == count(x₀, x₂)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (count(x₀, snoc(x₁, x₂)) == count(x₀, cons(x₂, nil))))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (append(filter(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (reverse(filter(x₀, x₁)) == nil))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: nat :: (map(x₀, snoc(y₀, y₁)) == append(map(x₀, y₀), cons(x₀[y₁], nil)))
    forall x₀: [nat]nat, x₁: [nat]Bool, x₂: list :: (not_(ex(x₁, x₂)) ==> (map(x₀, filter(x₁, x₂)) == nil))
    forall x₀: nat, y₀: list, y₁: list :: (remove(x₀, append(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (remove(x₀, snoc(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, cons(y₁, nil))))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(take(y₀, y₁), x₁) == append(take(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: [nat]nat, y₁: list, x₁: nat :: (snoc(map(y₀, y₁), x₁) == append(map(y₀, y₁), cons(x₁, nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(remove(y₀, y₁), x₁) == append(remove(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall y₀: [nat]Bool, y₁: list, x₁: nat :: (snoc(filter(y₀, y₁), x₁) == append(filter(y₀, y₁), cons(x₁, nil)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (snoc(filter(x₀, x₁), x₂) == cons(x₂, nil)))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (add(countif(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (filter(x₀, append(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, y₁)))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, append(x₁, x₂)) == filter(x₀, x₂)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (filter(x₀, snoc(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (filter(x₀, snoc(x₁, x₂)) == filter(x₀, cons(x₂, nil))))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (countif(x₀, append(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, y₁)))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, append(x₁, x₂)) == countif(x₀, x₂)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (countif(x₀, snoc(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (countif(x₀, snoc(x₁, x₂)) == countif(x₀, cons(x₂, nil))))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, x₁) == nil))
    forall x₀: [nat]Bool, x₁: list :: (all(x₀, x₁) ==> (filter(x₀, x₁) == x₁))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, x₁) == zero))
    forall x: list, y₀: [nat]Bool :: (all(y₀, x) ==> (countif(y₀, x) == length(x)))

### unique over thesy

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall x₀: [nat]nat, y₀: list :: (map(x₀, reverse(y₀)) == reverse(map(x₀, y₀)))
    forall x₀: [nat]nat, y₀: nat, y₁: list :: (map(x₀, rotate(y₀, y₁)) == rotate(y₀, map(x₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, x₁: list, x₂: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, append(x₁, x₂)) == count(x₀, x₂)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (count(x₀, snoc(x₁, x₂)) == count(x₀, cons(x₂, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (append(filter(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (reverse(filter(x₀, x₁)) == nil))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: nat :: (map(x₀, snoc(y₀, y₁)) == append(map(x₀, y₀), cons(x₀[y₁], nil)))
    forall x₀: [nat]nat, x₁: [nat]Bool, x₂: list :: (not_(ex(x₁, x₂)) ==> (map(x₀, filter(x₁, x₂)) == nil))
    forall x₀: nat, y₀: list, y₁: list :: (remove(x₀, append(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (remove(x₀, snoc(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (snoc(filter(x₀, x₁), x₂) == cons(x₂, nil)))
    forall x₀: nat, x₁: list, x₂: nat :: (not_(contains(x₀, x₁)) ==> (add(count(x₀, x₁), x₂) == x₂))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (add(countif(x₀, x₁), x₂) == x₂))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (filter(x₀, append(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, y₁)))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, append(x₁, x₂)) == filter(x₀, x₂)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (filter(x₀, snoc(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (filter(x₀, snoc(x₁, x₂)) == filter(x₀, cons(x₂, nil))))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (countif(x₀, append(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, y₁)))
    forall x₀: [nat]Bool, x₁: list, x₂: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, append(x₁, x₂)) == countif(x₀, x₂)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (countif(x₀, snoc(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, x₁: list, x₂: nat :: (not_(ex(x₀, x₁)) ==> (countif(x₀, snoc(x₁, x₂)) == countif(x₀, cons(x₂, nil))))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (count(x₀, x₁) == zero))
    forall x₀: nat, x₁: list :: (not_(contains(x₀, x₁)) ==> (remove(x₀, x₁) == x₁))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (filter(x₀, x₁) == nil))
    forall x₀: [nat]Bool, x₁: list :: (all(x₀, x₁) ==> (filter(x₀, x₁) == x₁))
    forall x₀: [nat]Bool, x₁: list :: (not_(ex(x₀, x₁)) ==> (countif(x₀, x₁) == zero))
    forall x: list, y₀: [nat]Bool :: (all(y₀, x) ==> (countif(y₀, x) == length(x)))


## lemmas confirmed by structural

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall x₀: [nat]nat, y₀: list :: (map(x₀, reverse(y₀)) == reverse(map(x₀, y₀)))
    forall x₀: [nat]nat, y₀: nat, y₁: list :: (map(x₀, rotate(y₀, y₁)) == rotate(y₀, map(x₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == append(reverse(y₁), reverse(y₀)))
    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: list :: (remove(x₀, append(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (remove(x₀, snoc(y₀, y₁)) == append(remove(x₀, y₀), remove(x₀, cons(y₁, nil))))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (filter(x₀, append(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (filter(x₀, snoc(y₀, y₁)) == append(filter(x₀, y₀), filter(x₀, cons(y₁, nil))))
    forall x₀: [nat]Bool, y₀: list, y₁: list :: (countif(x₀, append(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, y₁)))
    forall x₀: [nat]Bool, y₀: list, y₁: nat :: (countif(x₀, snoc(y₀, y₁)) == add(countif(x₀, y₀), countif(x₀, cons(y₁, nil))))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (take(x₀, map(y₀, y₁)) == map(y₀, take(x₀, y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]Bool, y₁: list :: (length(filter(y₀, y₁)) == countif(y₀, y₁))
    forall x₀: nat, y₀: [nat]nat, y₁: list :: (drop(x₀, map(y₀, y₁)) == map(y₀, drop(x₀, y₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat :: (reverse(snoc(y₀, y₁)) == cons(y₁, reverse(y₀)))
    forall x₀: [nat]nat, y₀: list, y₁: nat :: (map(x₀, snoc(y₀, y₁)) == append(map(x₀, y₀), cons(x₀[y₁], nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(take(y₀, y₁), x₁) == append(take(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: [nat]nat, y₁: list, x₁: nat :: (snoc(map(y₀, y₁), x₁) == append(map(y₀, y₁), cons(x₁, nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(remove(y₀, y₁), x₁) == append(remove(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall y₀: [nat]Bool, y₁: list, x₁: nat :: (snoc(filter(y₀, y₁), x₁) == append(filter(y₀, y₁), cons(x₁, nil)))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: list, y₀: list, z₀: nat :: ((y₀ == cons(z₀, nil)) ==> (append(x, y₀) == append(x, cons(z₀, nil))))


## lemmas confirmed by enumerate

### reduced

    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat :: (reverse(snoc(y₀, y₁)) == cons(y₁, reverse(y₀)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: list, y₀: list, z₀: nat :: ((y₀ == cons(z₀, nil)) ==> (append(x, y₀) == append(x, cons(z₀, nil))))


## lemmas confirmed by thesy

### reduced

    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat :: (reverse(snoc(y₀, y₁)) == cons(y₁, reverse(y₀)))
    forall y₀: [nat]nat, y₁: list, x₁: nat :: (snoc(map(y₀, y₁), x₁) == append(map(y₀, y₁), cons(x₁, nil)))
    forall y₀: nat, y₁: list, x₁: nat :: (snoc(remove(y₀, y₁), x₁) == append(remove(y₀, y₁), cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall y₀: nat, y₁: list, x₁: nat :: (snoc(take(y₀, y₁), x₁) == append(take(y₀, y₁), cons(x₁, nil)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall y₀: [nat]Bool, y₁: list, x₁: nat :: (snoc(filter(y₀, y₁), x₁) == append(filter(y₀, y₁), cons(x₁, nil)))
    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list, y₀: list, z₀: nat :: ((y₀ == cons(z₀, nil)) ==> (append(x, y₀) == append(x, cons(z₀, nil))))



# benchmark: evaluation/lemmas/list comparison for enumerate

## lemmas found by enumerate

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(append(y₀, nil), cons(y₁, x₁)))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall x₀: [nat]Bool, y₀: nat, y₁: list :: (filter(x₀, remove(y₀, y₁)) == remove(add(y₀, zero), filter(x₀, y₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(append(y₀, nil), snoc(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: [nat]Bool, y₁: list :: (add(x₀, countif(y₀, y₁)) == add(countif(y₀, y₁), add(x₀, zero)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall y₀: list, y₁: nat :: (length(snoc(y₀, y₁)) == add(length(y₀), succ(zero)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall x₀: nat, y₀: list :: (cons(x₀, reverse(y₀)) == reverse(snoc(y₀, x₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == take(length(y₀), snoc(y₀, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(y₀, y₁), x₀))
    forall y₀: list :: (reverse(reverse(y₀)) == rotate(zero, y₀))
    forall y₀: list :: (length(reverse(y₀)) == length(append(y₀, nil)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(reverse(y₁)))
    forall x₀: list, y₀: list, y₁: nat :: (append(x₀, snoc(y₀, y₁)) == snoc(append(x₀, y₀), add(y₁, zero)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(take(zero, y₀), rotate(zero, y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == drop(zero, drop(zero, y₀)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(rotate(zero, y₀), take(zero, y₀)))

### implied


### trivial

    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == append(drop(zero, x₀), reverse(y₀)))
    forall y₀: list, x₁: list :: (count(length(y₀), x₁) == count(length(y₀), rotate(zero, x₁)))
    forall y₀: nat, y₁: list, x₁: list :: (append(take(y₀, y₁), x₁) == append(take(y₀, y₁), rotate(zero, x₁)))


## unique lemmas found by enumerate

### overall unique

    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall x₀: [nat]Bool, y₀: nat, y₁: list :: (filter(x₀, remove(y₀, y₁)) == remove(add(y₀, zero), filter(x₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: [nat]Bool, y₁: list :: (add(x₀, countif(y₀, y₁)) == add(countif(y₀, y₁), add(x₀, zero)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == take(length(y₀), snoc(y₀, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(y₀, y₁), x₀))
    forall y₀: list :: (length(reverse(y₀)) == length(append(y₀, nil)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(reverse(y₁)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(take(zero, y₀), rotate(zero, y₀)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### unique over structural

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall x₀: [nat]Bool, y₀: nat, y₁: list :: (filter(x₀, remove(y₀, y₁)) == remove(add(y₀, zero), filter(x₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: [nat]Bool, y₁: list :: (add(x₀, countif(y₀, y₁)) == add(countif(y₀, y₁), add(x₀, zero)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == take(length(y₀), snoc(y₀, zero)))
    forall y₀: nat, y₁: list, x₁: list :: (append(take(y₀, y₁), x₁) == append(take(y₀, y₁), rotate(zero, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(y₀, y₁), x₀))
    forall y₀: list :: (length(reverse(y₀)) == length(append(y₀, nil)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(reverse(y₁)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(take(zero, y₀), rotate(zero, y₀)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### unique over conditional

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall x₀: [nat]Bool, y₀: nat, y₁: list :: (filter(x₀, remove(y₀, y₁)) == remove(add(y₀, zero), filter(x₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: [nat]Bool, y₁: list :: (add(x₀, countif(y₀, y₁)) == add(countif(y₀, y₁), add(x₀, zero)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == take(length(y₀), snoc(y₀, zero)))
    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == append(drop(zero, x₀), reverse(y₀)))
    forall y₀: list, x₁: list :: (count(length(y₀), x₁) == count(length(y₀), rotate(zero, x₁)))
    forall y₀: nat, y₁: list, x₁: list :: (append(take(y₀, y₁), x₁) == append(take(y₀, y₁), rotate(zero, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(y₀, y₁), x₀))
    forall y₀: list :: (length(reverse(y₀)) == length(append(y₀, nil)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(reverse(y₁)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(take(zero, y₀), rotate(zero, y₀)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(rotate(zero, y₀), take(zero, y₀)))

### unique over thesy

    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall x₀: [nat]Bool, y₀: nat, y₁: list :: (filter(x₀, remove(y₀, y₁)) == remove(add(y₀, zero), filter(x₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: [nat]Bool, y₁: list :: (add(x₀, countif(y₀, y₁)) == add(countif(y₀, y₁), add(x₀, zero)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: list :: (reverse(reverse(y₀)) == take(length(y₀), snoc(y₀, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(y₀, y₁), x₀))
    forall y₀: list :: (reverse(reverse(y₀)) == rotate(zero, y₀))
    forall y₀: list :: (length(reverse(y₀)) == length(append(y₀, nil)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(reverse(y₁)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(take(zero, y₀), rotate(zero, y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == drop(zero, drop(zero, y₀)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(rotate(zero, y₀), take(zero, y₀)))


## lemmas confirmed by structural

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(append(y₀, nil), cons(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(append(y₀, nil), snoc(y₁, x₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall x₀: nat, y₀: list :: (cons(x₀, reverse(y₀)) == reverse(snoc(y₀, x₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: list :: (reverse(reverse(y₀)) == rotate(zero, y₀))
    forall x₀: list, y₀: list, y₁: nat :: (append(x₀, snoc(y₀, y₁)) == snoc(append(x₀, y₀), add(y₁, zero)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(take(zero, y₀), rotate(zero, y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == drop(zero, drop(zero, y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(rotate(zero, y₀), take(zero, y₀)))

### implied

    forall y₀: list, y₁: nat :: (length(snoc(y₀, y₁)) == add(length(y₀), succ(zero)))

### trivial

    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == append(drop(zero, x₀), reverse(y₀)))
    forall y₀: list, x₁: list :: (count(length(y₀), x₁) == count(length(y₀), rotate(zero, x₁)))


## lemmas confirmed by conditional

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(append(y₀, nil), cons(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(append(y₀, nil), snoc(y₁, x₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall x₀: nat, y₀: list :: (cons(x₀, reverse(y₀)) == reverse(snoc(y₀, x₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: list :: (reverse(reverse(y₀)) == rotate(zero, y₀))
    forall x₀: list, y₀: list, y₁: nat :: (append(x₀, snoc(y₀, y₁)) == snoc(append(x₀, y₀), add(y₁, zero)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(take(zero, y₀), rotate(zero, y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == drop(zero, drop(zero, y₀)))
    forall y₀: list :: (reverse(reverse(y₀)) == append(rotate(zero, y₀), take(zero, y₀)))

### implied

    forall y₀: list, y₁: nat :: (length(snoc(y₀, y₁)) == add(length(y₀), succ(zero)))

### trivial



## lemmas confirmed by thesy

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(append(y₀, nil), snoc(y₁, x₁)))
    forall y₀: list, y₁: nat :: (length(snoc(y₀, y₁)) == add(length(y₀), succ(zero)))
    forall x₀: nat, y₀: list :: (cons(x₀, reverse(y₀)) == reverse(snoc(y₀, x₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall x₀: list, y₀: list, y₁: nat :: (append(x₀, snoc(y₀, y₁)) == snoc(append(x₀, y₀), add(y₁, zero)))

### implied


### trivial

    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(append(y₀, nil), cons(y₁, x₁)))
    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == append(drop(zero, x₀), reverse(y₀)))
    forall y₀: list, x₁: list :: (count(length(y₀), x₁) == count(length(y₀), rotate(zero, x₁)))
    forall y₀: nat, y₁: list, x₁: list :: (append(take(y₀, y₁), x₁) == append(take(y₀, y₁), rotate(zero, x₁)))



# benchmark: evaluation/lemmas/list comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == append(?ts_ph_list_0, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (length(snoc(?ts_ph_list_0, ?ts_ph_nat_1)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (reverse(snoc(?ts_ph_list_0, ?ts_ph_nat_0)) == cons(?ts_ph_nat_0, reverse(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (take(length(?ts_ph_list_0), ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (drop(length(?ts_ph_list_0), ?ts_ph_list_0) == nil)
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_0) == append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)) <==> true)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, ?ts_ph_list_0) == remove(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (rotate(?ts_ph_nat_0, cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))

### implied

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == drop(zero, ?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_0: list :: (cons(?ts_ph_nat_0, reverse(?ts_ph_list_0)) == reverse(snoc(?ts_ph_list_0, ?ts_ph_nat_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_0)) == snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)) == remove(?ts_ph_nat_1, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))

### trivial

    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (rotate(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (take(zero, ?ts_ph_list_0) == nil)
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)))


## unique lemmas found by thesy

### overall unique

    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (length(snoc(?ts_ph_list_0, ?ts_ph_nat_1)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (take(length(?ts_ph_list_0), ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (drop(length(?ts_ph_list_0), ?ts_ph_list_0) == nil)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)) <==> true)
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)))

### unique over structural

    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (length(snoc(?ts_ph_list_0, ?ts_ph_nat_1)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list :: (take(length(?ts_ph_list_0), ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (drop(length(?ts_ph_list_0), ?ts_ph_list_0) == nil)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)) <==> true)
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)))

### unique over conditional

    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == append(?ts_ph_list_0, nil))
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == drop(zero, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (length(snoc(?ts_ph_list_0, ?ts_ph_nat_1)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list :: (take(length(?ts_ph_list_0), ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (drop(length(?ts_ph_list_0), ?ts_ph_list_0) == nil)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)) <==> true)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (rotate(?ts_ph_nat_0, cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, nil))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)))

### unique over enumerate

    forall ?ts_ph_list_0: list :: (take(zero, ?ts_ph_list_0) == nil)
    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == append(?ts_ph_list_0, nil))
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == drop(zero, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (length(snoc(?ts_ph_list_0, ?ts_ph_nat_1)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (take(length(?ts_ph_list_0), ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (drop(length(?ts_ph_list_0), ?ts_ph_list_0) == nil)
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_0) == append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_0)) == snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (contains(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)) <==> true)
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, ?ts_ph_list_0) == remove(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)) == remove(?ts_ph_nat_1, ?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (rotate(?ts_ph_nat_0, cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, nil))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_1: list :: (drop(?ts_ph_nat_0, cons(?ts_ph_nat_0, ?ts_ph_list_1)) == drop(?ts_ph_nat_0, cons(zero, ?ts_ph_list_1)))


## lemmas confirmed by structural

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == append(?ts_ph_list_0, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (reverse(snoc(?ts_ph_list_0, ?ts_ph_nat_0)) == cons(?ts_ph_nat_0, reverse(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_0) == append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, ?ts_ph_list_0) == remove(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (rotate(?ts_ph_nat_0, cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))

### implied

    forall ?ts_ph_nat_0: nat, ?ts_ph_list_0: list :: (cons(?ts_ph_nat_0, reverse(?ts_ph_list_0)) == reverse(snoc(?ts_ph_list_0, ?ts_ph_nat_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_0)) == snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)) == remove(?ts_ph_nat_1, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))

### trivial

    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (rotate(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (take(zero, ?ts_ph_list_0) == nil)
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == drop(zero, ?ts_ph_list_0))


## lemmas confirmed by conditional

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == append(?ts_ph_list_0, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (reverse(snoc(?ts_ph_list_0, ?ts_ph_nat_0)) == cons(?ts_ph_nat_0, reverse(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_0) == append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, ?ts_ph_list_0) == remove(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))

### implied

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == drop(zero, ?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_0: list :: (cons(?ts_ph_nat_0, reverse(?ts_ph_list_0)) == reverse(snoc(?ts_ph_list_0, ?ts_ph_nat_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_0: nat :: (append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_0)) == snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (remove(?ts_ph_nat_1, snoc(?ts_ph_list_0, ?ts_ph_nat_1)) == remove(?ts_ph_nat_1, ?ts_ph_list_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (rotate(?ts_ph_nat_0, cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))

### trivial

    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (rotate(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (take(zero, ?ts_ph_list_0) == nil)


## lemmas confirmed by enumerate

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (reverse(snoc(?ts_ph_list_0, ?ts_ph_nat_0)) == cons(?ts_ph_nat_0, reverse(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))

### implied

    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_list_0: list :: (cons(?ts_ph_nat_0, reverse(?ts_ph_list_0)) == reverse(snoc(?ts_ph_list_0, ?ts_ph_nat_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))

### trivial

    forall ?ts_ph_list_0: list :: (drop(zero, ?ts_ph_list_0) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list :: (rotate(zero, ?ts_ph_list_0) == ?ts_ph_list_0)



