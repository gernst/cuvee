# benchmark: evaluation/lemmas/list/reverse comparison for structural

## lemmas found by structural

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(y₀, x₁))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == qreverse(y₁, reverse(y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == append(x₁, qreverse(y₁, reverse(y₀))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### implied

    forall y₀: list, y₁: list :: (reverse(qreverse(y₀, y₁)) == qreverse(y₁, y₀))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(qreverse(y₀, y₁), x₁) == append(x₁, qreverse(y₁, y₀)))
    forall x₀: list, x₁: list :: (nreverse(x₀, x₁) == append(x₁, reverse(x₀)))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)

### trivial



## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate


### unique over thesy



## lemmas confirmed by conditional

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(y₀, x₁))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == qreverse(y₁, reverse(y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == append(x₁, qreverse(y₁, reverse(y₀))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### implied

    forall y₀: list, y₁: list :: (reverse(qreverse(y₀, y₁)) == qreverse(y₁, y₀))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(qreverse(y₀, y₁), x₁) == append(x₁, qreverse(y₁, y₀)))
    forall x₀: list, x₁: list :: (nreverse(x₀, x₁) == append(x₁, reverse(x₀)))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)

### trivial



## lemmas confirmed by enumerate

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(y₀, x₁))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == qreverse(y₁, reverse(y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == append(x₁, qreverse(y₁, reverse(y₀))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### implied

    forall y₀: list, y₁: list :: (reverse(qreverse(y₀, y₁)) == qreverse(y₁, y₀))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(qreverse(y₀, y₁), x₁) == append(x₁, qreverse(y₁, y₀)))
    forall x₀: list, x₁: list :: (nreverse(x₀, x₁) == append(x₁, reverse(x₀)))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)

### trivial



## lemmas confirmed by thesy

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(y₀, x₁))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == qreverse(y₁, reverse(y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == append(x₁, qreverse(y₁, reverse(y₀))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### implied

    forall y₀: list, y₁: list :: (reverse(qreverse(y₀, y₁)) == qreverse(y₁, y₀))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(qreverse(y₀, y₁), x₁) == append(x₁, qreverse(y₁, y₀)))
    forall x₀: list, x₁: list :: (nreverse(x₀, x₁) == append(x₁, reverse(x₀)))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)

### trivial




# benchmark: evaluation/lemmas/list/reverse comparison for conditional

## lemmas found by conditional

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(y₀, x₁))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == qreverse(y₁, reverse(y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == append(x₁, qreverse(y₁, reverse(y₀))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### implied

    forall y₀: list, y₁: list :: (reverse(qreverse(y₀, y₁)) == qreverse(y₁, y₀))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(qreverse(y₀, y₁), x₁) == append(x₁, qreverse(y₁, y₀)))
    forall x₀: list, x₁: list :: (nreverse(x₀, x₁) == append(x₁, reverse(x₀)))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall x: list, y₀: list :: ((y₀ == nil) ==> (append(y₀, reverse(x)) == reverse(x)))


## unique lemmas found by conditional

### overall unique


### unique over structural


### unique over enumerate


### unique over thesy



## lemmas confirmed by structural

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(y₀, x₁))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == qreverse(y₁, reverse(y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == append(x₁, qreverse(y₁, reverse(y₀))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### implied

    forall y₀: list, y₁: list :: (reverse(qreverse(y₀, y₁)) == qreverse(y₁, y₀))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(qreverse(y₀, y₁), x₁) == append(x₁, qreverse(y₁, y₀)))
    forall x₀: list, x₁: list :: (nreverse(x₀, x₁) == append(x₁, reverse(x₀)))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall x: list, y₀: list :: ((y₀ == nil) ==> (append(y₀, reverse(x)) == reverse(x)))


## lemmas confirmed by enumerate

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(y₀, x₁))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == qreverse(y₁, reverse(y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == append(x₁, qreverse(y₁, reverse(y₀))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### implied

    forall y₀: list, y₁: list :: (reverse(qreverse(y₀, y₁)) == qreverse(y₁, y₀))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(qreverse(y₀, y₁), x₁) == append(x₁, qreverse(y₁, y₀)))
    forall x₀: list, x₁: list :: (nreverse(x₀, x₁) == append(x₁, reverse(x₀)))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall x: list, y₀: list :: ((y₀ == nil) ==> (append(y₀, reverse(x)) == reverse(x)))


## lemmas confirmed by thesy

### reduced

    forall y₀: list :: (reverse(reverse(y₀)) == y₀)
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(y₀, x₁))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == qreverse(y₁, reverse(y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == append(x₁, qreverse(y₁, reverse(y₀))))
    forall y₀: list, y₁: list, x₁: list :: (append(append(y₀, y₁), x₁) == append(y₀, append(y₁, x₁)))

### implied

    forall y₀: list, y₁: list :: (reverse(qreverse(y₀, y₁)) == qreverse(y₁, y₀))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(qreverse(y₀, y₁), x₁) == append(x₁, qreverse(y₁, y₀)))
    forall x₀: list, x₁: list :: (nreverse(x₀, x₁) == append(x₁, reverse(x₀)))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x: list :: (append(x, nil) == x)

### trivial

    forall x: list, y₀: list :: ((y₀ == nil) ==> (append(y₀, reverse(x)) == reverse(x)))



# benchmark: evaluation/lemmas/list/reverse comparison for enumerate

## lemmas found by enumerate

### reduced

    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list :: (reverse(y₀) == nreverse(y₀, nil))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x₀: list, y₀: list :: (qreverse(x₀, reverse(y₀)) == append(qreverse(x₀, nil), qreverse(y₀, nil)))
    forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == qreverse(y₁, cons(y₀, nil)))
    forall x₀: nat, y₀: list :: (cons(x₀, reverse(y₀)) == nreverse(y₀, cons(x₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, append(y₀, y₁)) == qreverse(qreverse(y₀, x₀), y₁))
    forall y₀: list, y₁: list :: (reverse(nreverse(y₀, y₁)) == qreverse(reverse(y₀), reverse(y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(append(y₀, nil), x₁))
    forall x₀: list, y₀: list :: (nreverse(x₀, reverse(y₀)) == qreverse(append(y₀, nil), nreverse(x₀, nil)))
    forall y₀: list, y₁: list, x₁: list :: (qreverse(append(y₀, y₁), x₁) == qreverse(y₁, qreverse(y₀, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == qreverse(qreverse(y₁, nil), qreverse(y₀, x₁)))
    forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, append(y₀, y₁)) == append(append(y₀, y₁), nreverse(x₀, nil)))
    forall x₀: nat, y₀: list, y₁: list :: (cons(x₀, append(y₀, y₁)) == nreverse(qreverse(y₁, nil), cons(x₀, y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == qreverse(nreverse(x₁, y₁), nreverse(y₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, qreverse(y₀, y₁)) == append(reverse(y₀), nreverse(x₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, qreverse(y₀, y₁)) == nreverse(qreverse(y₁, y₀), qreverse(x₀, nil)))

### implied

    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == qreverse(reverse(x₀), qreverse(y₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, nreverse(y₀, y₁)) == nreverse(nreverse(y₁, y₀), qreverse(x₀, nil)))
    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == qreverse(nreverse(x₀, nil), cons(y₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == nreverse(append(y₀, nil), nreverse(y₁, nil)))
    forall y₀: list, y₁: list, x₁: list :: (qreverse(nreverse(y₀, y₁), x₁) == append(y₀, qreverse(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == nreverse(qreverse(x₁, y₀), y₁))

### trivial



## unique lemmas found by enumerate

### overall unique


### unique over structural


### unique over conditional


### unique over thesy



## lemmas confirmed by structural

### reduced

    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list :: (reverse(y₀) == nreverse(y₀, nil))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x₀: list, y₀: list :: (qreverse(x₀, reverse(y₀)) == append(qreverse(x₀, nil), qreverse(y₀, nil)))
    forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == qreverse(y₁, cons(y₀, nil)))
    forall x₀: nat, y₀: list :: (cons(x₀, reverse(y₀)) == nreverse(y₀, cons(x₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, append(y₀, y₁)) == qreverse(qreverse(y₀, x₀), y₁))
    forall y₀: list, y₁: list :: (reverse(nreverse(y₀, y₁)) == qreverse(reverse(y₀), reverse(y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(append(y₀, nil), x₁))
    forall x₀: list, y₀: list :: (nreverse(x₀, reverse(y₀)) == qreverse(append(y₀, nil), nreverse(x₀, nil)))
    forall y₀: list, y₁: list, x₁: list :: (qreverse(append(y₀, y₁), x₁) == qreverse(y₁, qreverse(y₀, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == qreverse(qreverse(y₁, nil), qreverse(y₀, x₁)))
    forall x₀: nat, y₀: list, y₁: list :: (cons(x₀, append(y₀, y₁)) == nreverse(qreverse(y₁, nil), cons(x₀, y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == qreverse(nreverse(x₁, y₁), nreverse(y₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, qreverse(y₀, y₁)) == append(reverse(y₀), nreverse(x₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, qreverse(y₀, y₁)) == nreverse(qreverse(y₁, y₀), qreverse(x₀, nil)))

### implied

    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == qreverse(reverse(x₀), qreverse(y₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, nreverse(y₀, y₁)) == nreverse(nreverse(y₁, y₀), qreverse(x₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, append(y₀, y₁)) == append(append(y₀, y₁), nreverse(x₀, nil)))
    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == qreverse(nreverse(x₀, nil), cons(y₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == nreverse(append(y₀, nil), nreverse(y₁, nil)))
    forall y₀: list, y₁: list, x₁: list :: (qreverse(nreverse(y₀, y₁), x₁) == append(y₀, qreverse(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == nreverse(qreverse(x₁, y₀), y₁))

### trivial



## lemmas confirmed by conditional

### reduced

    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list :: (reverse(y₀) == nreverse(y₀, nil))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x₀: list, y₀: list :: (qreverse(x₀, reverse(y₀)) == append(qreverse(x₀, nil), qreverse(y₀, nil)))
    forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == qreverse(y₁, cons(y₀, nil)))
    forall x₀: nat, y₀: list :: (cons(x₀, reverse(y₀)) == nreverse(y₀, cons(x₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, append(y₀, y₁)) == qreverse(qreverse(y₀, x₀), y₁))
    forall y₀: list, y₁: list :: (reverse(nreverse(y₀, y₁)) == qreverse(reverse(y₀), reverse(y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(append(y₀, nil), x₁))
    forall x₀: list, y₀: list :: (nreverse(x₀, reverse(y₀)) == qreverse(append(y₀, nil), nreverse(x₀, nil)))
    forall y₀: list, y₁: list, x₁: list :: (qreverse(append(y₀, y₁), x₁) == qreverse(y₁, qreverse(y₀, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == qreverse(qreverse(y₁, nil), qreverse(y₀, x₁)))
    forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, append(y₀, y₁)) == append(append(y₀, y₁), nreverse(x₀, nil)))
    forall x₀: nat, y₀: list, y₁: list :: (cons(x₀, append(y₀, y₁)) == nreverse(qreverse(y₁, nil), cons(x₀, y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == qreverse(nreverse(x₁, y₁), nreverse(y₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, qreverse(y₀, y₁)) == append(reverse(y₀), nreverse(x₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, qreverse(y₀, y₁)) == nreverse(qreverse(y₁, y₀), qreverse(x₀, nil)))

### implied

    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == qreverse(reverse(x₀), qreverse(y₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, nreverse(y₀, y₁)) == nreverse(nreverse(y₁, y₀), qreverse(x₀, nil)))
    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == qreverse(nreverse(x₀, nil), cons(y₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == nreverse(append(y₀, nil), nreverse(y₁, nil)))
    forall y₀: list, y₁: list, x₁: list :: (qreverse(nreverse(y₀, y₁), x₁) == append(y₀, qreverse(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == nreverse(qreverse(x₁, y₀), y₁))

### trivial



## lemmas confirmed by thesy

### reduced

    forall x₁: list :: (x₁ == append(x₁, nil))
    forall y₀: list :: (reverse(y₀) == nreverse(y₀, nil))
    forall y₀: list, y₁: list, x₁: list :: (append(qreverse(y₀, y₁), x₁) == qreverse(y₀, append(y₁, x₁)))
    forall x₀: list, y₀: list :: (qreverse(x₀, reverse(y₀)) == append(qreverse(x₀, nil), qreverse(y₀, nil)))
    forall y₀: nat, y₁: list :: (append(reverse(y₁), cons(y₀, nil)) == qreverse(y₁, cons(y₀, nil)))
    forall x₀: nat, y₀: list :: (cons(x₀, reverse(y₀)) == nreverse(y₀, cons(x₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, append(y₀, y₁)) == qreverse(qreverse(y₀, x₀), y₁))
    forall y₀: list, y₁: list :: (reverse(nreverse(y₀, y₁)) == qreverse(reverse(y₀), reverse(y₁)))
    forall x₀: list, y₀: list, y₁: list :: (append(x₀, append(y₀, y₁)) == append(append(x₀, y₀), append(y₁, nil)))
    forall y₀: list, x₁: list :: (append(reverse(y₀), x₁) == qreverse(append(y₀, nil), x₁))
    forall x₀: list, y₀: list :: (nreverse(x₀, reverse(y₀)) == qreverse(append(y₀, nil), nreverse(x₀, nil)))
    forall y₀: list, y₁: list, x₁: list :: (qreverse(append(y₀, y₁), x₁) == qreverse(y₁, qreverse(y₀, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == qreverse(qreverse(y₁, nil), qreverse(y₀, x₁)))
    forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, append(y₀, y₁)) == append(append(y₀, y₁), nreverse(x₀, nil)))
    forall x₀: nat, y₀: list, y₁: list :: (cons(x₀, append(y₀, y₁)) == nreverse(qreverse(y₁, nil), cons(x₀, y₀)))
    forall y₀: list, y₁: list, x₁: list :: (nreverse(append(y₀, y₁), x₁) == qreverse(nreverse(x₁, y₁), nreverse(y₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (nreverse(x₀, qreverse(y₀, y₁)) == append(reverse(y₀), nreverse(x₀, y₁)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, qreverse(y₀, y₁)) == nreverse(qreverse(y₁, y₀), qreverse(x₀, nil)))

### implied

    forall x₀: list, y₀: list :: (append(x₀, reverse(y₀)) == qreverse(reverse(x₀), qreverse(y₀, nil)))
    forall x₀: list, y₀: list, y₁: list :: (qreverse(x₀, nreverse(y₀, y₁)) == nreverse(nreverse(y₁, y₀), qreverse(x₀, nil)))
    forall x₀: list, y₀: nat, y₁: list :: (append(x₀, cons(y₀, y₁)) == qreverse(nreverse(x₀, nil), cons(y₀, y₁)))
    forall y₀: list, y₁: list :: (reverse(append(y₀, y₁)) == nreverse(append(y₀, nil), nreverse(y₁, nil)))
    forall y₀: list, y₁: list, x₁: list :: (qreverse(nreverse(y₀, y₁), x₁) == append(y₀, qreverse(y₁, x₁)))
    forall y₀: list, y₁: list, x₁: list :: (append(nreverse(y₀, y₁), x₁) == nreverse(qreverse(x₁, y₀), y₁))

### trivial




# benchmark: evaluation/lemmas/list/reverse comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_list_0: list :: (nreverse(?ts_ph_list_0, nil) == reverse(?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (reverse(append(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, reverse(?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (cons(?ts_ph_nat_1, nreverse(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (nreverse(?ts_ph_list_0, nreverse(?ts_ph_list_1, ?ts_ph_list_2)) == nreverse(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qreverse(qreverse(?ts_ph_list_0, ?ts_ph_list_1), nil) == qreverse(?ts_ph_list_1, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, append(?ts_ph_list_0, ?ts_ph_list_1)) == append(?ts_ph_list_0, nreverse(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, append(?ts_ph_list_0, reverse(?ts_ph_list_0))))
    forall ?ts_ph_list_0: list :: (append(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)) == nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (reverse(reverse(?ts_ph_list_0)) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qreverse(?ts_ph_list_0, ?ts_ph_list_1) == append(reverse(?ts_ph_list_0), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, ?ts_ph_list_1) == nreverse(reverse(?ts_ph_list_1), ?ts_ph_list_0))

### implied

    forall ?ts_ph_list_0: list :: (reverse(?ts_ph_list_0) == nreverse(?ts_ph_list_0, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, reverse(?ts_ph_list_1)) == reverse(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == cons(?ts_ph_nat_1, nreverse(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (nreverse(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == nreverse(?ts_ph_list_0, nreverse(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list :: (qreverse(?ts_ph_list_1, ?ts_ph_list_0) == qreverse(qreverse(?ts_ph_list_0, ?ts_ph_list_1), nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, nreverse(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (cons(?ts_ph_nat_1, append(?ts_ph_list_0, reverse(?ts_ph_list_0))) == nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), cons(?ts_ph_nat_1, nil)))
    forall ?ts_ph_list_0: list :: (nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)) == append(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(reverse(?ts_ph_list_0), ?ts_ph_list_1) == qreverse(?ts_ph_list_0, ?ts_ph_list_1))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list :: (nreverse(reverse(?ts_ph_list_1), ?ts_ph_list_0) == append(?ts_ph_list_0, ?ts_ph_list_1))

### trivial



## unique lemmas found by thesy

### overall unique


### unique over structural


### unique over conditional


### unique over enumerate



## lemmas confirmed by structural

### reduced

    forall ?ts_ph_list_0: list :: (nreverse(?ts_ph_list_0, nil) == reverse(?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (reverse(append(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, reverse(?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (cons(?ts_ph_nat_1, nreverse(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (nreverse(?ts_ph_list_0, nreverse(?ts_ph_list_1, ?ts_ph_list_2)) == nreverse(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qreverse(qreverse(?ts_ph_list_0, ?ts_ph_list_1), nil) == qreverse(?ts_ph_list_1, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, append(?ts_ph_list_0, ?ts_ph_list_1)) == append(?ts_ph_list_0, nreverse(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, append(?ts_ph_list_0, reverse(?ts_ph_list_0))))
    forall ?ts_ph_list_0: list :: (append(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)) == nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (reverse(reverse(?ts_ph_list_0)) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qreverse(?ts_ph_list_0, ?ts_ph_list_1) == append(reverse(?ts_ph_list_0), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, ?ts_ph_list_1) == nreverse(reverse(?ts_ph_list_1), ?ts_ph_list_0))

### implied

    forall ?ts_ph_list_0: list :: (reverse(?ts_ph_list_0) == nreverse(?ts_ph_list_0, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, reverse(?ts_ph_list_1)) == reverse(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == cons(?ts_ph_nat_1, nreverse(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (nreverse(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == nreverse(?ts_ph_list_0, nreverse(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list :: (qreverse(?ts_ph_list_1, ?ts_ph_list_0) == qreverse(qreverse(?ts_ph_list_0, ?ts_ph_list_1), nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, nreverse(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (cons(?ts_ph_nat_1, append(?ts_ph_list_0, reverse(?ts_ph_list_0))) == nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), cons(?ts_ph_nat_1, nil)))
    forall ?ts_ph_list_0: list :: (nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)) == append(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(reverse(?ts_ph_list_0), ?ts_ph_list_1) == qreverse(?ts_ph_list_0, ?ts_ph_list_1))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list :: (nreverse(reverse(?ts_ph_list_1), ?ts_ph_list_0) == append(?ts_ph_list_0, ?ts_ph_list_1))

### trivial



## lemmas confirmed by conditional

### reduced

    forall ?ts_ph_list_0: list :: (nreverse(?ts_ph_list_0, nil) == reverse(?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (reverse(append(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, reverse(?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (cons(?ts_ph_nat_1, nreverse(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qreverse(qreverse(?ts_ph_list_0, ?ts_ph_list_1), nil) == qreverse(?ts_ph_list_1, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, append(?ts_ph_list_0, reverse(?ts_ph_list_0))))
    forall ?ts_ph_list_0: list :: (append(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)) == nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (reverse(reverse(?ts_ph_list_0)) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qreverse(?ts_ph_list_0, ?ts_ph_list_1) == append(reverse(?ts_ph_list_0), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, ?ts_ph_list_1) == nreverse(reverse(?ts_ph_list_1), ?ts_ph_list_0))

### implied

    forall ?ts_ph_list_0: list :: (reverse(?ts_ph_list_0) == nreverse(?ts_ph_list_0, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, reverse(?ts_ph_list_1)) == reverse(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == cons(?ts_ph_nat_1, nreverse(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (nreverse(?ts_ph_list_0, nreverse(?ts_ph_list_1, ?ts_ph_list_2)) == nreverse(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (nreverse(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == nreverse(?ts_ph_list_0, nreverse(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list :: (qreverse(?ts_ph_list_1, ?ts_ph_list_0) == qreverse(qreverse(?ts_ph_list_0, ?ts_ph_list_1), nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, append(?ts_ph_list_0, ?ts_ph_list_1)) == append(?ts_ph_list_0, nreverse(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, nreverse(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (cons(?ts_ph_nat_1, append(?ts_ph_list_0, reverse(?ts_ph_list_0))) == nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), cons(?ts_ph_nat_1, nil)))
    forall ?ts_ph_list_0: list :: (nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)) == append(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(reverse(?ts_ph_list_0), ?ts_ph_list_1) == qreverse(?ts_ph_list_0, ?ts_ph_list_1))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list :: (nreverse(reverse(?ts_ph_list_1), ?ts_ph_list_0) == append(?ts_ph_list_0, ?ts_ph_list_1))

### trivial



## lemmas confirmed by enumerate

### reduced

    forall ?ts_ph_list_0: list :: (nreverse(?ts_ph_list_0, nil) == reverse(?ts_ph_list_0))
    forall ?ts_ph_list_0: list :: (append(?ts_ph_list_0, nil) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (reverse(append(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, reverse(?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (cons(?ts_ph_nat_1, nreverse(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)) == append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (nreverse(?ts_ph_list_0, nreverse(?ts_ph_list_1, ?ts_ph_list_2)) == nreverse(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qreverse(qreverse(?ts_ph_list_0, ?ts_ph_list_1), nil) == qreverse(?ts_ph_list_1, ?ts_ph_list_0))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, append(?ts_ph_list_0, ?ts_ph_list_1)) == append(?ts_ph_list_0, nreverse(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat :: (nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), cons(?ts_ph_nat_1, nil)) == cons(?ts_ph_nat_1, append(?ts_ph_list_0, reverse(?ts_ph_list_0))))
    forall ?ts_ph_list_0: list :: (append(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)) == nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list :: (reverse(reverse(?ts_ph_list_0)) == ?ts_ph_list_0)
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (qreverse(?ts_ph_list_0, ?ts_ph_list_1) == append(reverse(?ts_ph_list_0), ?ts_ph_list_1))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, ?ts_ph_list_1) == nreverse(reverse(?ts_ph_list_1), ?ts_ph_list_0))

### implied

    forall ?ts_ph_list_0: list :: (reverse(?ts_ph_list_0) == nreverse(?ts_ph_list_0, nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, reverse(?ts_ph_list_1)) == reverse(append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_nat_1: nat, ?ts_ph_list_1: list :: (nreverse(?ts_ph_list_0, cons(?ts_ph_nat_1, ?ts_ph_list_1)) == cons(?ts_ph_nat_1, nreverse(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (append(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == append(?ts_ph_list_0, append(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list, ?ts_ph_list_2: list :: (nreverse(append(?ts_ph_list_0, ?ts_ph_list_1), ?ts_ph_list_2) == nreverse(?ts_ph_list_0, nreverse(?ts_ph_list_1, ?ts_ph_list_2)))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list :: (qreverse(?ts_ph_list_1, ?ts_ph_list_0) == qreverse(qreverse(?ts_ph_list_0, ?ts_ph_list_1), nil))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(?ts_ph_list_0, nreverse(?ts_ph_list_0, ?ts_ph_list_1)) == nreverse(?ts_ph_list_0, append(?ts_ph_list_0, ?ts_ph_list_1)))
    forall ?ts_ph_nat_1: nat, ?ts_ph_list_0: list :: (cons(?ts_ph_nat_1, append(?ts_ph_list_0, reverse(?ts_ph_list_0))) == nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), cons(?ts_ph_nat_1, nil)))
    forall ?ts_ph_list_0: list :: (nreverse(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)) == append(nreverse(?ts_ph_list_0, ?ts_ph_list_0), nreverse(?ts_ph_list_0, ?ts_ph_list_0)))
    forall ?ts_ph_list_0: list, ?ts_ph_list_1: list :: (append(reverse(?ts_ph_list_0), ?ts_ph_list_1) == qreverse(?ts_ph_list_0, ?ts_ph_list_1))
    forall ?ts_ph_list_1: list, ?ts_ph_list_0: list :: (nreverse(reverse(?ts_ph_list_1), ?ts_ph_list_0) == append(?ts_ph_list_0, ?ts_ph_list_1))

### trivial




