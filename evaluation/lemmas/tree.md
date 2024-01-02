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
    forall x: nat :: (add(x, zero) == x)

### unique over thesy



## lemmas confirmed by conditional

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


## lemmas confirmed by enumerate

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


## lemmas confirmed by thesy

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
    forall x: nat :: (add(x, zero) == x)

### unique over thesy



## lemmas confirmed by structural

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


## lemmas confirmed by enumerate

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


## lemmas confirmed by thesy

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

### implied

    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(add(y₀, x₀), succ(zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(x₁, y₁), add(y₀, zero)))
    forall y₀: nat :: (succ(y₀) == add(y₀, succ(zero)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₁), length(y₀)))

### trivial

    forall y₀: tree :: (mirror(mirror(y₀)) == y₀)


## unique lemmas found by enumerate

### overall unique


### unique over structural

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: nat, y₁: tree :: (size(insert(y₀, y₁)) == size(insert(zero, y₁)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))
    forall y₀: tree :: (succ(size(y₀)) == size(insert(zero, y₀)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(add(y₀, x₀), succ(zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(x₁, y₁), add(y₀, zero)))
    forall y₀: nat :: (succ(y₀) == add(y₀, succ(zero)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₁), length(y₀)))

### unique over conditional

    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: list, x₁: nat :: (add(length(y₀), x₁) == add(add(x₁, zero), length(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₀, add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(x₁, add(y₁, y₀)))
    forall y₀: nat, y₁: tree :: (size(insert(y₀, y₁)) == size(insert(zero, y₁)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))
    forall y₀: tree :: (succ(size(y₀)) == size(insert(zero, y₀)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(add(y₀, x₀), succ(zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(x₁, y₁), add(y₀, zero)))
    forall y₀: nat :: (succ(y₀) == add(y₀, succ(zero)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₁), length(y₀)))

### unique over thesy



## lemmas confirmed by structural

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == add(size(y₁), zero))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: [nat]nat, y₁: tree :: (elems(maptree(y₀, y₁)) == map(y₀, elems(y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == length(elems(y₁)))
    forall y₀: tree :: (length(elems(y₀)) == size(y₀))

### implied


### trivial

    forall y₀: tree :: (mirror(mirror(y₀)) == y₀)


## lemmas confirmed by conditional

### reduced

    forall y₀: nat :: (y₀ == add(y₀, zero))
    forall x₁: list :: (x₁ == append(x₁, nil))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), y₁))
    forall x₀: [nat]nat, y₀: list, y₁: list :: (map(x₀, append(y₀, y₁)) == append(map(x₀, y₀), map(x₀, y₁)))
    forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == add(size(y₁), zero))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₀), length(y₁)))
    forall y₀: [nat]nat, y₁: tree :: (elems(maptree(y₀, y₁)) == map(y₀, elems(y₁)))
    forall y₀: [nat]nat, y₁: list :: (length(map(y₀, y₁)) == length(y₁))
    forall y₀: [nat]nat, y₁: tree :: (size(maptree(y₀, y₁)) == length(elems(y₁)))
    forall y₀: tree :: (length(elems(y₀)) == size(y₀))

### implied


### trivial

    forall y₀: tree :: (mirror(mirror(y₀)) == y₀)


## lemmas confirmed by thesy

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

### implied

    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(x₁, succ(y₀)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(add(y₀, x₀), succ(zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(x₁, y₁), add(y₀, zero)))
    forall y₀: nat :: (succ(y₀) == add(y₀, succ(zero)))
    forall y₀: list, y₁: list :: (length(append(y₀, y₁)) == add(length(y₁), length(y₀)))

### trivial

    forall y₀: tree :: (mirror(mirror(y₀)) == y₀)



# benchmark: evaluation/lemmas/tree comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_1: nat, ?ts_ph_tree_0: tree :: (size(insert(?ts_ph_nat_1, ?ts_ph_tree_0)) == succ(size(?ts_ph_tree_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_list_0: list :: (length(map(?ts_ph_POfn_nat_natPC_0, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_tree_0: tree :: (size(maptree(?ts_ph_POfn_nat_natPC_0, ?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_1)) == map(?ts_ph_POfn_nat_natPC_1, append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_tree_0: tree :: (length(elems(?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (elems(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)) == map(?ts_ph_POfn_nat_natPC_1, elems(?ts_ph_tree_0)))

### implied

    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (map(?ts_ph_POfn_nat_natPC_1, append(?ts_ph_list_0, ?ts_ph_list_1)) == append(map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_tree_0: tree :: (size(mirror(?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_tree_0: tree :: (size(?ts_ph_tree_0) == size(mirror(?ts_ph_tree_0)))
    forall ?ts_ph_tree_0: tree :: (size(?ts_ph_tree_0) == length(elems(?ts_ph_tree_0)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (map(?ts_ph_POfn_nat_natPC_1, elems(?ts_ph_tree_0)) == elems(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)))

### trivial

    forall ?ts_ph_tree_0: tree :: (mirror(mirror(?ts_ph_tree_0)) == ?ts_ph_tree_0)
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (mirror(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)) == maptree(?ts_ph_POfn_nat_natPC_1, mirror(?ts_ph_tree_0)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (maptree(?ts_ph_POfn_nat_natPC_1, mirror(?ts_ph_tree_0)) == mirror(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)))


## unique lemmas found by thesy

### overall unique

    forall ?ts_ph_tree_0: tree :: (size(mirror(?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_tree_0: tree :: (size(?ts_ph_tree_0) == size(mirror(?ts_ph_tree_0)))

### unique over structural

    forall ?ts_ph_nat_1: nat, ?ts_ph_tree_0: tree :: (size(insert(?ts_ph_nat_1, ?ts_ph_tree_0)) == succ(size(?ts_ph_tree_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_tree_0: tree :: (size(mirror(?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_tree_0: tree :: (size(?ts_ph_tree_0) == size(mirror(?ts_ph_tree_0)))

### unique over conditional

    forall ?ts_ph_nat_1: nat, ?ts_ph_tree_0: tree :: (size(insert(?ts_ph_nat_1, ?ts_ph_tree_0)) == succ(size(?ts_ph_tree_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_tree_0: tree :: (size(mirror(?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_tree_0: tree :: (size(?ts_ph_tree_0) == size(mirror(?ts_ph_tree_0)))

### unique over enumerate

    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (mirror(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)) == maptree(?ts_ph_POfn_nat_natPC_1, mirror(?ts_ph_tree_0)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (maptree(?ts_ph_POfn_nat_natPC_1, mirror(?ts_ph_tree_0)) == mirror(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)))
    forall ?ts_ph_tree_0: tree :: (size(mirror(?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_tree_0: tree :: (size(?ts_ph_tree_0) == size(mirror(?ts_ph_tree_0)))


## lemmas confirmed by structural

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_list_0: list :: (length(map(?ts_ph_POfn_nat_natPC_0, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_tree_0: tree :: (size(maptree(?ts_ph_POfn_nat_natPC_0, ?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_1)) == map(?ts_ph_POfn_nat_natPC_1, append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_tree_0: tree :: (length(elems(?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (elems(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)) == map(?ts_ph_POfn_nat_natPC_1, elems(?ts_ph_tree_0)))

### implied

    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (map(?ts_ph_POfn_nat_natPC_1, append(?ts_ph_list_0, ?ts_ph_list_1)) == append(map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_1)))
    forall ?ts_ph_tree_0: tree :: (size(?ts_ph_tree_0) == length(elems(?ts_ph_tree_0)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (map(?ts_ph_POfn_nat_natPC_1, elems(?ts_ph_tree_0)) == elems(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)))

### trivial

    forall ?ts_ph_tree_0: tree :: (mirror(mirror(?ts_ph_tree_0)) == ?ts_ph_tree_0)
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (mirror(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)) == maptree(?ts_ph_POfn_nat_natPC_1, mirror(?ts_ph_tree_0)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (maptree(?ts_ph_POfn_nat_natPC_1, mirror(?ts_ph_tree_0)) == mirror(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)))


## lemmas confirmed by conditional

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_list_0: list :: (length(map(?ts_ph_POfn_nat_natPC_0, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_tree_0: tree :: (size(maptree(?ts_ph_POfn_nat_natPC_0, ?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_1)) == map(?ts_ph_POfn_nat_natPC_1, append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_tree_0: tree :: (length(elems(?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (elems(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)) == map(?ts_ph_POfn_nat_natPC_1, elems(?ts_ph_tree_0)))

### implied

    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (map(?ts_ph_POfn_nat_natPC_1, append(?ts_ph_list_0, ?ts_ph_list_1)) == append(map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_1)))
    forall ?ts_ph_tree_0: tree :: (size(?ts_ph_tree_0) == length(elems(?ts_ph_tree_0)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (map(?ts_ph_POfn_nat_natPC_1, elems(?ts_ph_tree_0)) == elems(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)))

### trivial

    forall ?ts_ph_tree_0: tree :: (mirror(mirror(?ts_ph_tree_0)) == ?ts_ph_tree_0)
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (mirror(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)) == maptree(?ts_ph_POfn_nat_natPC_1, mirror(?ts_ph_tree_0)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (maptree(?ts_ph_POfn_nat_natPC_1, mirror(?ts_ph_tree_0)) == mirror(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)))


## lemmas confirmed by enumerate

### reduced

    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_1: nat, ?ts_ph_tree_0: tree :: (size(insert(?ts_ph_nat_1, ?ts_ph_tree_0)) == succ(size(?ts_ph_tree_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_list_0: list :: (length(map(?ts_ph_POfn_nat_natPC_0, ?ts_ph_list_0)) == length(?ts_ph_list_0))
    forall ?ts_ph_POfn_nat_natPC_0: [nat]nat, ?ts_ph_tree_0: tree :: (size(maptree(?ts_ph_POfn_nat_natPC_0, ?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (add(length(?ts_ph_list_0), length(?ts_ph_list_1)) == length(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_1)) == map(?ts_ph_POfn_nat_natPC_1, append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == add(?ts_ph_nat_1, ?ts_ph_nat_0))
    forall ?ts_ph_tree_0: tree :: (length(elems(?ts_ph_tree_0)) == size(?ts_ph_tree_0))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (elems(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)) == map(?ts_ph_POfn_nat_natPC_1, elems(?ts_ph_tree_0)))

### implied

    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (length(append(?ts_ph_list_0, ?ts_ph_list_1)) == add(length(?ts_ph_list_0), length(?ts_ph_list_1)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (map(?ts_ph_POfn_nat_natPC_1, append(?ts_ph_list_0, ?ts_ph_list_1)) == append(map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_0), map(?ts_ph_POfn_nat_natPC_1, ?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_1, ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_tree_0: tree :: (size(?ts_ph_tree_0) == length(elems(?ts_ph_tree_0)))
    forall ?ts_ph_POfn_nat_natPC_1: [nat]nat, ?ts_ph_tree_0: tree :: (map(?ts_ph_POfn_nat_natPC_1, elems(?ts_ph_tree_0)) == elems(maptree(?ts_ph_POfn_nat_natPC_1, ?ts_ph_tree_0)))

### trivial

    forall ?ts_ph_tree_0: tree :: (mirror(mirror(?ts_ph_tree_0)) == ?ts_ph_tree_0)



