# benchmark: evaluation/lemmas/list/append comparison for structural

## lemmas found by structural

### reduced

    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))

### trivial



## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate

    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))

### unique over thesy

    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))


## lemmas confirmed by conditional

### reduced

    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))

### trivial



## lemmas confirmed by enumerate

### reduced

    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### trivial



## lemmas confirmed by thesy

### reduced

    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))

### trivial




# benchmark: evaluation/lemmas/list/append comparison for conditional

## lemmas found by conditional

### reduced

    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))

### trivial

    forall x: list, y₀: list, z₀: nat :: ((y₀ == cons(z₀, nil)) ==> (append(x, y₀) == append(x, cons(z₀, nil))))


## unique lemmas found by conditional

### overall unique


### unique over structural


### unique over enumerate

    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))

### unique over thesy

    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))


## lemmas confirmed by structural

### reduced

    forall x₀: nat, y₀: list, y₁: list :: (count(x₀, append(y₀, y₁)) == add(count(x₀, y₀), count(x₀, y₁)))
    forall x₀: nat, y₀: list, y₁: nat :: (count(x₀, snoc(y₀, y₁)) == add(count(x₀, y₀), count(x₀, cons(y₁, nil))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))

### trivial

    forall x: list, y₀: list, z₀: nat :: ((y₀ == cons(z₀, nil)) ==> (append(x, y₀) == append(x, cons(z₀, nil))))


## lemmas confirmed by enumerate

### reduced

    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### trivial

    forall x: list, y₀: list, z₀: nat :: ((y₀ == cons(z₀, nil)) ==> (append(x, y₀) == append(x, cons(z₀, nil))))


## lemmas confirmed by thesy

### reduced

    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, x₁)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(y₀, append(y₁, cons(x₁, nil))))
    forall x₀: list, x₁: nat :: (snoc(x₀, x₁) == append(x₀, cons(x₁, nil)))
    forall x: list :: (append(x, nil) == x)
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: list, y₁: nat, x₁: nat :: (snoc(snoc(y₀, y₁), x₁) == append(y₀, cons(y₁, cons(x₁, nil))))

### trivial

    forall x: list, y₀: list, z₀: nat :: ((y₀ == cons(z₀, nil)) ==> (append(x, y₀) == append(x, cons(z₀, nil))))



# benchmark: evaluation/lemmas/list/append comparison for enumerate

## lemmas found by enumerate

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(append(y₀, nil), cons(y₁, x₁)))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(append(y₀, nil), snoc(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall y₀: list, y₁: nat :: (length(snoc(y₀, y₁)) == add(length(y₀), succ(zero)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))

### implied

    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall x₀: list, y₀: nat, y₁: nat :: (snoc(x₀, add(y₀, y₁)) == snoc(append(x₀, nil), add(y₁, y₀)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### trivial



## unique lemmas found by enumerate

### overall unique

    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))

### unique over structural

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: list, y₀: nat, y₁: nat :: (snoc(x₀, add(y₀, y₁)) == snoc(append(x₀, nil), add(y₁, y₀)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### unique over conditional

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall x₀: list, y₀: nat, y₁: nat :: (snoc(x₀, add(y₀, y₁)) == snoc(append(x₀, nil), add(y₁, y₀)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### unique over thesy

    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))


## lemmas confirmed by structural

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(append(y₀, nil), cons(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(append(y₀, nil), snoc(y₁, x₁)))
    forall y₀: list, y₁: nat :: (length(snoc(y₀, y₁)) == add(length(y₀), succ(zero)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))

### implied

    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))

### trivial



## lemmas confirmed by conditional

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(append(y₀, nil), cons(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(append(y₀, nil), snoc(y₁, x₁)))
    forall y₀: list, y₁: nat :: (length(snoc(y₀, y₁)) == add(length(y₀), succ(zero)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))

### implied

    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))

### trivial



## lemmas confirmed by thesy

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list, y₁: nat, x₁: list :: (append(snoc(y₀, y₁), x₁) == append(append(y₀, nil), cons(y₁, x₁)))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: list, y₁: list, x₁: nat :: (snoc(append(y₀, y₁), x₁) == append(append(y₀, nil), snoc(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: list :: (add(x₀, count(y₀, y₁)) == add(count(y₀, y₁), x₀))
    forall y₀: list, y₁: nat :: (length(snoc(y₀, y₁)) == add(length(y₀), succ(zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))

### implied

    forall x₀: list, y₀: nat, y₁: nat :: (snoc(x₀, add(y₀, y₁)) == snoc(append(x₀, nil), add(y₁, y₀)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))

### trivial




# benchmark: evaluation/lemmas/list/append comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (length(snoc(?ts_ph_list_0, ?ts_ph_nat_0)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat :: (succ(succ(?ts_ph_nat_0)) == add(succ(?ts_ph_nat_0), succ(zero)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_1: nat :: (append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_1)) == snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_1))

### implied

    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list :: (succ(length(?ts_ph_list_0)) == add(length(?ts_ph_list_0), succ(zero)))
    forall ?ts_ph_list_0: list :: (add(length(?ts_ph_list_0), succ(zero)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat :: (add(succ(?ts_ph_nat_0), succ(zero)) == succ(succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_1: nat :: (snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_1) == append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_1)))

### trivial



## unique lemmas found by thesy

### overall unique


### unique over structural

    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (length(snoc(?ts_ph_list_0, ?ts_ph_nat_0)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (succ(length(?ts_ph_list_0)) == add(length(?ts_ph_list_0), succ(zero)))
    forall ?ts_ph_list_0: list :: (add(length(?ts_ph_list_0), succ(zero)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat :: (succ(succ(?ts_ph_nat_0)) == add(succ(?ts_ph_nat_0), succ(zero)))
    forall ?ts_ph_nat_0: nat :: (add(succ(?ts_ph_nat_0), succ(zero)) == succ(succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))

### unique over conditional

    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (length(snoc(?ts_ph_list_0, ?ts_ph_nat_0)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (succ(length(?ts_ph_list_0)) == add(length(?ts_ph_list_0), succ(zero)))
    forall ?ts_ph_list_0: list :: (add(length(?ts_ph_list_0), succ(zero)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat :: (succ(succ(?ts_ph_nat_0)) == add(succ(?ts_ph_nat_0), succ(zero)))
    forall ?ts_ph_nat_0: nat :: (add(succ(?ts_ph_nat_0), succ(zero)) == succ(succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))

### unique over enumerate



## lemmas confirmed by structural

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_1: nat :: (append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_1)) == snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_1))

### implied

    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_1: nat :: (snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_1) == append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_1)))

### trivial



## lemmas confirmed by conditional

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_1: nat :: (append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_1)) == snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_1))

### implied

    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_1: nat :: (snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_1) == append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_1)))

### trivial



## lemmas confirmed by enumerate

### reduced

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_nat_0: nat :: (length(snoc(?ts_ph_list_0, ?ts_ph_nat_0)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat :: (succ(succ(?ts_ph_nat_0)) == add(succ(?ts_ph_nat_0), succ(zero)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_1: nat :: (append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_1)) == snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_1))

### implied

    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (append(snoc(?ts_ph_list_0, ?ts_ph_nat_1), ?ts_ph_list_1) == append(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list :: (succ(length(?ts_ph_list_0)) == add(length(?ts_ph_list_0), succ(zero)))
    forall ?ts_ph_list_0: list :: (add(length(?ts_ph_list_0), succ(zero)) == succ(length(?ts_ph_list_0)))
    forall ?ts_ph_nat_0: nat :: (add(succ(?ts_ph_nat_0), succ(zero)) == succ(succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_nat_1: nat :: (snoc(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_nat_1) == append(?ts_ph_list_0, snoc(?ts_ph_list_1, ?ts_ph_nat_1)))

### trivial




