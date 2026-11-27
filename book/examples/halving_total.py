def halving_total(value: int) -> int:
    total = 0
    while value > 0:
        total += value
        value //= 2
    return total
