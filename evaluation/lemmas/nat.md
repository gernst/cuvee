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

    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall y₀: nat, y₁: nat :: (not_(leq(y₀, y₁)) <==> lt(y₁, y₀))
    forall y₀: nat, y₁: nat :: (not_(lt(y₀, y₁)) <==> leq(y₁, y₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, min(y₀, y₁)) == max(min(y₀, y₁), x₀))
    forall y₀: nat, y₁: nat, x₁: nat :: (leq(sub(y₀, y₁), x₁) <==> leq(y₀, add(y₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (lt(x₀, sub(y₀, y₁)) <==> lt(add(y₁, x₀), y₀))

### unique over thesy

    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall y₀: nat, y₁: nat :: (not_(leq(y₀, y₁)) <==> lt(y₁, y₀))
    forall y₀: nat, y₁: nat, x₁: nat :: (leq(sub(y₀, y₁), x₁) <==> leq(y₀, add(y₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (lt(x₀, sub(y₀, y₁)) <==> lt(add(y₁, x₀), y₀))


## lemmas confirmed by conditional

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


## lemmas confirmed by enumerate

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: nat :: (max(x, zero) == x)


## lemmas confirmed by thesy

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, min(y₀, y₁)) == max(min(y₀, y₁), x₀))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: nat, y₁: nat :: (not_(lt(y₀, y₁)) <==> leq(y₁, y₀))

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: nat :: (max(x, zero) == x)



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
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (leq(x₀, sub(x₁, x₂)) <==> leq(x₀, zero)))
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
    forall x₀: nat, x₁: nat :: (lt(x₀, x₁) ==> (sub(x₀, x₁) == zero))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (max(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (max(x₀, x₁) == x₀))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (min(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (min(x₀, x₁) == x₀))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (max(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (mul(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (add(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (min(x₀, sub(x₁, x₂)) == min(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(sub(x₀, x₁), x₂) <==> lt(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(min(x₀, x₁), x₂) <==> false))
    forall y₀: nat, y₁: nat :: (not_(lt(y₀, y₁)) <==> leq(y₁, y₀))

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: nat :: (max(x, zero) == x)


## unique lemmas found by conditional

### overall unique

    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (sub(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(sub(x₀, x₁), x₂) == sub(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, max(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(x₀, add(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, min(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (max(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (max(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (leq(min(x₀, x₁), x₂) ==> (max(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (leq(x₀, sub(x₁, x₂)) <==> leq(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (leq(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (leq(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (leq(add(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, min(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (mul(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (add(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (min(x₀, sub(x₁, x₂)) == min(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, max(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(max(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(x₀, add(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (min(add(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, min(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(sub(x₀, x₁), x₂) <==> lt(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (lt(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (lt(add(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(min(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat :: (lt(x₀, x₁) ==> (sub(x₀, x₁) == zero))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (max(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (max(x₀, x₁) == x₀))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (min(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (min(x₀, x₁) == x₀))

### unique over structural

    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (sub(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(sub(x₀, x₁), x₂) == sub(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, max(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(x₀, add(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, min(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (max(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (max(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (leq(min(x₀, x₁), x₂) ==> (max(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (leq(x₀, sub(x₁, x₂)) <==> leq(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (leq(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (leq(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (leq(add(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, min(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (mul(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (add(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (min(x₀, sub(x₁, x₂)) == min(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, max(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(max(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(x₀, add(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (min(add(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, min(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(sub(x₀, x₁), x₂) <==> lt(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (lt(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (lt(add(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(min(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat :: (lt(x₀, x₁) ==> (sub(x₀, x₁) == zero))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (max(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (max(x₀, x₁) == x₀))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (min(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (min(x₀, x₁) == x₀))

### unique over enumerate

    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (sub(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(sub(x₀, x₁), x₂) == sub(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, max(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(x₀, add(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, min(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (max(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (max(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (leq(min(x₀, x₁), x₂) ==> (max(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (leq(x₀, sub(x₁, x₂)) <==> leq(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (leq(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (leq(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (leq(add(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, min(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (mul(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (add(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (min(x₀, sub(x₁, x₂)) == min(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, max(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(max(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(x₀, add(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (min(add(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, min(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(sub(x₀, x₁), x₂) <==> lt(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (lt(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (lt(add(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(min(x₀, x₁), x₂) <==> false))
    forall y₀: nat, y₁: nat :: (not_(leq(y₀, y₁)) <==> lt(y₁, y₀))
    forall y₀: nat, y₁: nat :: (not_(lt(y₀, y₁)) <==> leq(y₁, y₀))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, min(y₀, y₁)) == max(min(y₀, y₁), x₀))
    forall y₀: nat, y₁: nat, x₁: nat :: (leq(sub(y₀, y₁), x₁) <==> leq(y₀, add(y₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (lt(x₀, sub(y₀, y₁)) <==> lt(add(y₁, x₀), y₀))
    forall x₀: nat, x₁: nat :: (lt(x₀, x₁) ==> (sub(x₀, x₁) == zero))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (max(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (max(x₀, x₁) == x₀))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (min(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (min(x₀, x₁) == x₀))

### unique over thesy

    forall y₀: nat, y₁: nat, x₁: nat :: (mul(add(y₀, y₁), x₁) == add(mul(y₀, x₁), mul(y₁, x₁)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (sub(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(sub(x₀, x₁), x₂) == sub(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, max(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (sub(x₀, add(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (sub(x₀, min(x₁, x₂)) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (max(x₀, sub(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (max(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (leq(min(x₀, x₁), x₂) ==> (max(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (leq(x₀, sub(x₁, x₂)) <==> leq(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (leq(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (leq(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (leq(add(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (leq(x₀, min(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (mul(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (add(sub(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₁, x₂) ==> (min(x₀, sub(x₁, x₂)) == min(x₀, zero)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(sub(x₀, x₁), x₂) == zero))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, max(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(max(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (min(x₀, add(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (min(add(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (min(x₀, min(x₁, x₂)) == x₀))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (min(min(x₀, x₁), x₂) == x₂))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(sub(x₀, x₁), x₂) <==> lt(zero, x₂)))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, min(x₁, x₂)) ==> (lt(x₀, max(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(max(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₀, x₁) ==> (lt(x₀, add(x₁, x₂)) <==> true))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, x₀) ==> (lt(add(x₀, x₁), x₂) <==> false))
    forall x₀: nat, x₁: nat, x₂: nat :: (lt(x₂, min(x₀, x₁)) ==> (lt(min(x₀, x₁), x₂) <==> false))
    forall y₀: nat, y₁: nat :: (not_(leq(y₀, y₁)) <==> lt(y₁, y₀))
    forall y₀: nat, y₁: nat, x₁: nat :: (leq(sub(y₀, y₁), x₁) <==> leq(y₀, add(y₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (lt(x₀, sub(y₀, y₁)) <==> lt(add(y₁, x₀), y₀))
    forall x₀: nat, x₁: nat :: (lt(x₀, x₁) ==> (sub(x₀, x₁) == zero))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (max(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (max(x₀, x₁) == x₀))
    forall x₀: nat, x₁: nat :: (lt(x₁, x₀) ==> (min(x₀, x₁) == x₁))
    forall x₀: nat, x₁: nat :: (leq(x₀, x₁) ==> (min(x₀, x₁) == x₀))


## lemmas confirmed by structural

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


## lemmas confirmed by enumerate

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x: nat :: (add(x, zero) == x)

### implied


### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: nat :: (max(x, zero) == x)


## lemmas confirmed by thesy

### reduced

    forall y₀: nat, y₁: nat, x₁: nat :: (add(add(y₀, y₁), x₁) == add(y₀, add(y₁, x₁)))
    forall x₀: nat, y₀: nat, y₁: nat :: (max(x₀, min(y₀, y₁)) == max(min(y₀, y₁), x₀))
    forall x: nat :: (add(x, zero) == x)

### implied

    forall y₀: nat, y₁: nat :: (not_(lt(y₀, y₁)) <==> leq(y₁, y₀))

### trivial

    forall y₀: Bool :: (not_(not_(y₀)) <==> y₀)
    forall x: nat :: (max(x, zero) == x)



