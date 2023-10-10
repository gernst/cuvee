# benchmark: evaluation/lemmas/nat comparison for structural

## lemmas found by structural

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall y₀: nat, y₁: nat :: (not_(leq(y₀, y₁)) <==> lt(y₁, y₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, min(y₀, y₁)) == max(min(y₀, y₁), x₀))
    forall y₀: nat, y₁: nat, x₁: nat :: (leq(sub(y₀, y₁), x₁) <==> leq(y₀, add(y₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (lt(x₀, sub(y₀, y₁)) <==> lt(add(y₁, x₀), y₀))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: nat, y₁: nat :: (not_(lt(y₀, y₁)) <==> leq(y₁, y₀))

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: nat :: (max(x, zero) == x)


## unique lemmas found by structural

### overall unique


### unique over conditional


### unique over enumerate


### unique over thesy




# benchmark: evaluation/lemmas/nat comparison for conditional

## lemmas found by conditional

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (sub(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(sub(x₀, x₁), x₂) == sub(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, max(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(x₀, add(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, min(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (max(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (leq(min(x₀, x₁), x₂) ==> (max(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (leq(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (leq(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (leq(add(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, min(x₁, x₂)) <==> true))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, max(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(max(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(x₀, add(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (min(add(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, min(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (lt(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (lt(add(x₀, x₁), x₂) <==> false))
    forall y₀: nat, y₁: nat :: (not_(leq(y₀, y₁)) <==> lt(y₁, y₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, min(y₀, y₁)) == max(min(y₀, y₁), x₀))
    forall y₀: nat, y₁: nat, x₁: nat :: (leq(sub(y₀, y₁), x₁) <==> leq(y₀, add(y₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (lt(x₀, sub(y₀, y₁)) <==> lt(add(y₁, x₀), y₀))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (max(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (max(x₀, x₁) == x₀))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (min(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (min(x₀, x₁) == x₀))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (max(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (leq(x₀, sub(x₁, x₂)) <==> leq(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (mul(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (add(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (min(x₀, sub(x₁, x₂)) == min(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(sub(x₀, x₁), x₂) <==> lt(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(min(x₀, x₁), x₂) <==> false))
    forall y₀: nat, y₁: nat :: (not_(lt(y₀, y₁)) <==> leq(y₁, y₀))
    forall x₀: nat, x₁: nat :: (lt(x₀, x₁) ==> (sub(x₀, x₁) == zero))

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: nat :: (max(x, zero) == x)


## unique lemmas found by conditional

### overall unique


### unique over structural


### unique over enumerate


### unique over thesy




# benchmark: evaluation/lemmas/nat comparison for enumerate

## lemmas found by enumerate

### reduced

    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, max(y₀, y₁)) == mul(add(x₀, zero), max(y₀, y₁)))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(y₀, succ(y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(sub(y₀, y₁), x₁) == add(sub(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(mul(y₀, y₁), x₁) == add(mul(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(max(y₀, y₀), succ(y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, sub(y₀, y₁)) == max(max(x₀, zero), sub(y₀, y₁)))
    forall y₀: nat, x₁: nat :: (sub(succ(y₀), x₁) == sub(succ(y₀), max(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, sub(y₀, y₁)) == sub(max(x₀, zero), sub(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, min(y₀, y₁)) == mul(max(x₀, x₀), min(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(max(y₀, zero), add(x₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(max(y₀, y₁), x₁) == add(max(y₀, y₁), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(max(x₁, zero), add(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), y₁))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, max(y₀, y₁)) == add(max(y₀, y₁), max(x₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(min(y₀, y₁), x₁) == add(min(x₁, x₁), min(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(max(y₀, y₁), x₁) == max(max(y₀, y₁), max(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, min(y₀, y₁)) == max(max(x₀, x₀), min(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(add(y₀, y₁), x₁) == min(add(y₁, y₀), min(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(min(y₀, y₀), add(x₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(max(y₀, y₁), x₁) == add(min(x₁, x₁), max(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(add(y₀, y₁), x₁) == max(add(y₀, y₁), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(min(y₀, y₁), x₁) == max(min(y₀, y₁), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, min(y₀, y₁)) == sub(add(x₀, zero), min(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, add(y₀, y₁)) == max(min(x₀, x₀), add(y₁, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, max(y₀, y₁)) == max(min(x₀, x₀), max(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(add(y₀, y₁), x₁) == max(add(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(max(y₀, y₁), x₁) == min(max(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(min(y₀, y₁), x₁) == sub(min(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(sub(y₀, y₁), x₁) == mul(sub(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(max(y₀, y₁), x₁) == max(max(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == mul(add(y₁, y₀), min(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, min(y₀, y₁)) == min(add(x₀, y₀), add(x₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), add(y₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(max(y₀, y₁), x₁) == mul(max(y₀, y₁), min(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, mul(y₀, y₁)) == min(min(x₀, x₀), mul(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(mul(y₀, y₁), x₁) == mul(mul(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(sub(y₀, y₁), x₁) == sub(sub(y₀, y₁), min(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, min(y₀, y₁)) == min(min(x₀, x₀), min(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(min(y₀, y₁), x₁) == mul(min(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(max(y₀, y₁), x₁) == sub(max(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), min(y₁, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, zero), add(y₁, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(max(y₀, zero), add(y₁, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, mul(y₀, y₁)) == mul(min(x₀, x₀), mul(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(min(y₀, y₀), add(y₁, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(add(y₀, y₁), x₁) == sub(add(y₁, y₀), min(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), min(y₁, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, zero), add(y₀, y₁)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(add(x₀, zero), succ(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(mul(y₀, y₁), x₁) == add(mul(y₀, y₁), min(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(min(x₀, x₀), add(y₀, y₁)))
    forall y₀: nat, y₁: nat :: (succ(add(y₀, y₁)) == add(min(y₀, y₀), succ(y₁)))
    forall x₀: nat, y₀: nat :: (mul(x₀, succ(y₀)) == add(x₀, mul(x₀, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == mul(max(x₀, zero), add(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, add(y₀, y₁)) == min(max(x₀, zero), add(y₀, y₁)))
    forall y₀: nat, x₁: nat :: (add(y₀, x₁) == add(y₀, max(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, max(y₀, y₁)) == add(max(x₀, zero), max(y₀, y₁)))
    forall y₀: nat, x₁: nat :: (add(x₁, mul(y₀, x₁)) == add(max(x₁, x₁), mul(y₀, max(x₁, x₁))))
    forall y₀: nat, x₁: nat :: (add(x₁, mul(y₀, x₁)) == add(max(x₁, zero), mul(y₀, max(x₁, zero))))
    forall y₀: nat, x₁: nat :: (add(x₁, mul(y₀, x₁)) == add(add(x₁, zero), mul(y₀, add(x₁, zero))))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == succ(add(y₀, max(x₀, zero))))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == mul(add(y₁, y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, add(y₀, y₁)) == max(add(x₀, zero), add(y₁, y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(min(y₀, y₁), x₁) == min(min(y₀, y₁), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == mul(add(y₀, y₁), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == mul(add(x₀, zero), add(y₀, y₁)))
    forall y₀: nat, x₁: nat :: (add(x₁, mul(y₀, x₁)) == add(min(x₁, x₁), mul(y₀, min(x₁, x₁))))

### implied

    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, sub(y₀, y₁)) == min(max(x₀, zero), sub(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, sub(y₀, y₁)) == max(min(x₀, x₀), sub(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, y₁), max(x₁, zero)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(max(x₀, zero), succ(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₁, y₀), max(x₁, zero)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(max(x₁, x₁), succ(y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, add(y₀, y₁)) == max(max(x₀, zero), add(y₁, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(y₀, y₁), min(x₀, x₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(add(y₀, y₁), x₁) == max(add(y₀, y₁), max(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(x₀, y₀), y₁))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(max(y₀, y₁), x₁) == min(max(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == mul(add(y₁, y₀), max(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, min(y₀, y₁)) == sub(max(x₀, zero), min(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(sub(y₀, y₁), x₁) == mul(sub(y₀, y₁), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, add(y₀, y₁)) == min(max(x₀, zero), add(y₁, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, min(y₀, y₁)) == min(add(x₀, zero), min(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, sub(y₀, y₁)) == max(max(x₀, x₀), sub(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(mul(y₀, y₁), x₁) == min(mul(y₀, y₁), max(x₁, zero)))
    forall x₀: nat, y₀: nat :: (max(x₀, succ(y₀)) == max(add(x₀, zero), succ(y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, add(y₀, y₁)) == min(add(x₀, zero), add(y₀, y₁)))
    forall x₀: nat, y₀: nat :: (sub(x₀, succ(y₀)) == sub(add(x₀, zero), succ(y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(max(y₀, y₁), x₁) == mul(max(y₀, y₁), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(max(y₀, y₁), x₁) == min(max(y₀, y₁), max(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, min(y₀, y₁)) == mul(max(x₀, zero), min(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(min(y₀, y₁), x₁) == max(min(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, x₁: nat :: (add(y₀, x₁) == add(x₁, min(y₀, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, add(y₀, y₁)) == mul(max(x₀, zero), add(y₁, y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(add(y₀, y₁), x₁) == sub(add(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, x₁: nat :: (succ(add(y₀, x₁)) == add(add(x₁, y₀), succ(zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, add(y₀, y₁)) == sub(max(x₀, zero), add(y₁, y₀)))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(sub(y₀, y₁), x₁) == min(sub(y₀, y₁), min(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(min(y₀, y₁), x₁) == max(min(y₀, y₁), max(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, max(y₀, y₁)) == sub(max(x₀, x₀), max(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(sub(y₀, y₁), x₁) == sub(sub(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(max(y₀, y₁), x₁) == sub(max(y₀, y₁), max(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, min(y₀, y₁)) == max(min(x₀, x₀), min(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(sub(y₀, y₁), x₁) == sub(sub(y₀, y₁), max(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(sub(y₀, y₁), x₁) == min(sub(y₀, y₁), max(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, max(y₀, y₁)) == min(max(x₀, zero), max(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, max(y₀, y₁)) == max(max(x₀, zero), max(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(max(y₀, y₁), x₁) == max(max(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (max(mul(y₀, y₁), x₁) == max(mul(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(sub(y₀, y₁), x₁) == mul(sub(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat :: (succ(mul(y₀, y₁)) == add(mul(y₀, y₁), succ(zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, min(y₀, y₁)) == min(max(x₀, x₀), min(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, max(y₀, y₁)) == mul(max(x₀, zero), max(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(mul(y₀, y₁), x₁) == sub(mul(y₀, y₁), max(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(max(y₀, y₁), x₁) == mul(max(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(add(y₀, y₁), x₁) == sub(add(y₁, y₀), max(x₁, x₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(max(y₀, y₁), x₁) == sub(max(y₀, y₁), max(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, min(y₀, y₁)) == max(max(x₀, zero), min(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, mul(y₀, y₁)) == min(max(x₀, zero), mul(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (sub(min(y₀, y₁), x₁) == sub(min(y₀, y₁), max(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, mul(y₀, y₁)) == max(max(x₀, zero), mul(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, mul(y₀, y₁)) == mul(max(x₀, zero), mul(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(x₁, y₁), add(y₀, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(add(y₀, x₁), add(y₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, min(y₀, y₁)) == min(max(x₀, zero), min(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(add(y₀, y₁), x₁) == min(add(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(min(y₀, y₁), x₁) == mul(min(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (min(min(y₀, y₁), x₁) == min(min(y₀, y₁), max(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(min(x₁, x₁), add(y₀, y₁)))
    forall y₀: nat :: (succ(y₀) == add(y₀, succ(zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, mul(y₀, y₁)) == mul(max(x₀, x₀), mul(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (mul(sub(y₀, y₁), x₁) == mul(sub(y₀, y₁), max(x₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, sub(y₀, y₁)) == add(sub(y₀, y₁), add(x₀, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (min(x₀, sub(y₀, y₁)) == min(max(x₀, x₀), sub(y₀, y₁)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(min(y₀, y₀), succ(x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(y₀, y₁), add(x₀, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(max(y₀, zero), add(x₁, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, mul(y₀, y₁)) == add(add(x₀, zero), mul(y₀, y₁)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₁, add(y₀, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(y₀, y₁), max(x₀, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(sub(y₀, y₁), x₁) == add(sub(y₀, y₁), add(x₁, zero)))
    forall y₀: nat, y₁: nat, x₁: nat :: (add(min(y₀, y₁), x₁) == add(min(y₀, y₁), add(x₁, zero)))
    forall y₀: nat, y₁: nat :: (add(y₀, y₁) == add(y₁, add(y₀, zero)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(add(y₀, zero), succ(x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, min(y₀, y₁)) == sub(max(x₀, x₀), min(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, mul(y₀, y₁)) == sub(max(x₀, x₀), mul(y₀, y₁)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == succ(add(x₀, min(y₀, y₀))))
    forall y₀: nat, x₁: nat :: (max(succ(y₀), x₁) == max(succ(y₀), add(x₁, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(min(y₁, y₁), add(x₀, y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(y₁, add(y₀, x₀)))
    forall x₀: nat, y₀: nat :: (mul(x₀, succ(y₀)) == add(mul(x₀, y₀), max(x₀, zero)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, sub(y₀, y₁)) == sub(max(x₀, x₀), sub(y₀, y₁)))
    forall x₀: nat, y₀: nat :: (add(x₀, succ(y₀)) == add(max(y₀, zero), succ(x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(max(y₁, zero), add(y₀, x₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (add(x₀, add(y₀, y₁)) == add(add(y₁, y₀), max(x₀, x₀)))

### trivial

    forall x₀: nat, y₀: nat :: (min(x₀, succ(y₀)) == min(max(x₀, zero), succ(y₀)))
    forall x₀: nat, y₀: nat :: (sub(x₀, succ(y₀)) == sub(max(x₀, zero), succ(y₀)))
    forall x₀: nat, y₀: nat, y₁: nat :: (sub(x₀, mul(y₀, y₁)) == sub(max(x₀, zero), mul(y₀, y₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (mul(x₀, sub(y₀, y₁)) == mul(max(x₀, zero), sub(y₀, y₁)))


## unique lemmas found by enumerate

### overall unique


### unique over structural


### unique over conditional


### unique over thesy




# benchmark: evaluation/lemmas/nat comparison for thesy

## lemmas found by thesy

### reduced

    forall ?ts_ph_nat_0: nat :: (max(?ts_ph_nat_0, ?ts_ph_nat_0) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat :: (min(?ts_ph_nat_0, ?ts_ph_nat_0) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, ?ts_ph_nat_0) <==> true)
    forall ?ts_ph_nat_0: nat :: (sub(?ts_ph_nat_0, ?ts_ph_nat_0) == zero)
    forall ?ts_ph_nat_0: nat :: (mul(?ts_ph_nat_0, zero) == zero)
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, zero) == max(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (lt(?ts_ph_nat_0, ?ts_ph_nat_0) <==> false)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(?ts_ph_nat_0, ?ts_ph_nat_1) <==> lt(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, succ(?ts_ph_nat_1)) == succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat :: (min(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, succ(?ts_ph_nat_0)) <==> true)
    forall ?ts_ph_nat_0: nat :: (lt(succ(?ts_ph_nat_0), ?ts_ph_nat_0) <==> false)
    forall ?ts_ph_nat_0: nat :: (sub(succ(?ts_ph_nat_0), ?ts_ph_nat_0) == succ(zero))
    forall ?ts_ph_nat_0: nat :: (min(?ts_ph_nat_0, succ(zero)) == min(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (max(succ(zero), ?ts_ph_nat_0) == max(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (max(succ(?ts_ph_nat_0), ?ts_ph_nat_0) == max(?ts_ph_nat_0, succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (add(?ts_ph_nat_0, succ(zero)) == max(?ts_ph_nat_0, succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2) == add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (leq(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> true)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (lt(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) <==> false)
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == max(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (add(?ts_ph_nat_0, ?ts_ph_nat_1) == max(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (lt(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) <==> lt(zero, ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (sub(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == sub(?ts_ph_nat_0, succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (min(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == min(?ts_ph_nat_0, succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (min(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == min(succ(?ts_ph_nat_0), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (min(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == mul(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (mul(?ts_ph_nat_0, ?ts_ph_nat_0) == max(mul(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_0) <==> not_(lt(zero, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (not_(lt(zero, ?ts_ph_nat_0)) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (min(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == min(?ts_ph_nat_0, mul(?ts_ph_nat_0, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (min(mul(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_0) == min(succ(?ts_ph_nat_0), ?ts_ph_nat_0))

### implied

    forall ?ts_ph_nat_0: nat :: (max(?ts_ph_nat_0, zero) == add(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (lt(?ts_ph_nat_0, succ(?ts_ph_nat_1)) <==> leq(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (succ(add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, succ(?ts_ph_nat_1)))
    forall ?ts_ph_nat_0: nat :: (min(succ(zero), ?ts_ph_nat_0) == min(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat :: (max(?ts_ph_nat_0, succ(zero)) == max(succ(zero), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (max(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == max(succ(?ts_ph_nat_0), ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (max(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == add(?ts_ph_nat_0, succ(zero)))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat, ?ts_ph_nat_2: nat :: (add(?ts_ph_nat_0, add(?ts_ph_nat_1, ?ts_ph_nat_2)) == add(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_2))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (max(add(?ts_ph_nat_0, ?ts_ph_nat_1), ?ts_ph_nat_0) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat, ?ts_ph_nat_1: nat :: (max(?ts_ph_nat_0, add(?ts_ph_nat_0, ?ts_ph_nat_1)) == add(?ts_ph_nat_0, ?ts_ph_nat_1))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, mul(?ts_ph_nat_0, ?ts_ph_nat_0)) <==> true)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(add(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (max(mul(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_0) == mul(?ts_ph_nat_0, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (mul(succ(?ts_ph_nat_0), succ(zero)) == max(?ts_ph_nat_0, succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (max(?ts_ph_nat_0, succ(?ts_ph_nat_0)) == mul(succ(?ts_ph_nat_0), succ(zero)))
    forall ?ts_ph_nat_0: nat :: (min(?ts_ph_nat_0, mul(?ts_ph_nat_0, ?ts_ph_nat_0)) == min(?ts_ph_nat_0, succ(?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (min(succ(?ts_ph_nat_0), ?ts_ph_nat_0) == min(mul(?ts_ph_nat_0, ?ts_ph_nat_0), ?ts_ph_nat_0))

### trivial

    forall ?ts_ph_nat_0: nat :: (max(?ts_ph_nat_0, zero) == ?ts_ph_nat_0)
    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == zero)
    forall ?ts_ph_nat_0: nat :: (min(?ts_ph_nat_0, zero) == zero)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> not_(lt(zero, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (not_(lt(zero, ?ts_ph_nat_0)) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (lt(zero, ?ts_ph_nat_0) <==> not_(leq(?ts_ph_nat_0, zero)))
    forall ?ts_ph_nat_0: nat :: (not_(leq(?ts_ph_nat_0, zero)) <==> lt(zero, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))


## unique lemmas found by thesy

### overall unique

    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))

### unique over structural

    forall ?ts_ph_nat_0: nat :: (min(?ts_ph_nat_0, zero) == zero)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))

### unique over conditional

    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))

### unique over enumerate

    forall ?ts_ph_nat_0: nat :: (sub(zero, ?ts_ph_nat_0) == zero)
    forall ?ts_ph_nat_0: nat :: (min(?ts_ph_nat_0, zero) == zero)
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> not_(lt(zero, ?ts_ph_nat_0)))
    forall ?ts_ph_nat_0: nat :: (not_(lt(zero, ?ts_ph_nat_0)) <==> leq(?ts_ph_nat_0, zero))
    forall ?ts_ph_nat_0: nat :: (lt(zero, ?ts_ph_nat_0) <==> not_(leq(?ts_ph_nat_0, zero)))
    forall ?ts_ph_nat_0: nat :: (not_(leq(?ts_ph_nat_0, zero)) <==> lt(zero, ?ts_ph_nat_0))
    forall ?ts_ph_nat_0: nat :: (leq(?ts_ph_nat_0, zero) <==> leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero))
    forall ?ts_ph_nat_0: nat :: (leq(mul(?ts_ph_nat_0, ?ts_ph_nat_0), zero) <==> leq(?ts_ph_nat_0, zero))



