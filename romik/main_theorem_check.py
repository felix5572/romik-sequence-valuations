"""Check Theorem 1.1 of the paper on the computed values of Romik's sequence d(n).

For every prime p = 3 (mod 4) below `prime_bound` and every n in the data, with A = 4n,
m = floor(A/(p+1)) and r = n - m(p+1)/4, the script requires

    (i)   v_p(d(n)) >= v_p(A!) - v_p((p m)!),
    (ii)  p delta((p+1)/4) is a p-adic unit and
          p^m m! delta(n) = (p delta((p+1)/4))^m delta(r)  (mod p),   delta(k) = 2^k d(k)/(4k)!,
          and equality holds in (i) if and only if p does not divide d(r),

and prints the data quoted in Section 8 of the paper: the number of primes for which equality
always holds, the residue classes r with p | d(r), and the points where the excess
v_p(d(n)) - v_p(A!) + v_p((p m)!) differs from v_p(d(r)).

Usage: python3 main_theorem_check.py <d_pickle> <prime_bound>
"""
import pickle
import sys

from checks import require


def valuation(x: int, p: int) -> int:
    require(x != 0)
    count = 0
    while x % p == 0:
        x //= p
        count += 1
    return count


def factorial_valuation(n: int, p: int) -> int:
    total = 0
    while n:
        n //= p
        total += n
    return total


def lower_bound(n: int, p: int) -> int:
    m = 4 * n // (p + 1)
    return factorial_valuation(4 * n, p) - factorial_valuation(p * m, p)


def residue(n: int, p: int) -> int:
    return n - (4 * n // (p + 1)) * (p + 1) // 4


def primes_three_mod_four(bound: int) -> tuple:
    return tuple(p for p in range(3, bound, 4) if all(p % q for q in range(3, int(p**0.5) + 1, 2)))


def unit_part(x: int, p: int) -> int:
    """x / p^v_p(x) modulo p."""
    require(x != 0)
    while x % p == 0:
        x //= p
    return x % p


def factorial_unit_parts(count: int, p: int) -> tuple:
    """(k! / p^v_p(k!) mod p) for k = 0..count."""
    out = [1]
    for k in range(1, count + 1):
        out.append(out[-1] * unit_part(k, p) % p)
    return tuple(out)


def residue_mod_p(value: int, unit: int) -> int:
    """Residue modulo p of a p-integral number with the given valuation and unit part."""
    require(value >= 0)
    return unit if value == 0 else 0


def check_prime(d: tuple, p: int) -> tuple:
    """(residue classes r with p | d(r), points where the excess differs from v_p(d(r)))."""
    period = (p + 1) // 4
    require(period < len(d), (p, len(d)))
    divisible_classes = tuple(r for r in range(period) if d[r] % p == 0)
    d_value = tuple(valuation(x, p) for x in d)
    d_unit = tuple(unit_part(x, p) for x in d)
    fact_unit = factorial_unit_parts(4 * len(d), p)
    # nu = p * delta((p+1)/4) = p 2^q d(q) / (p+1)!, and v_p((p+1)!) = 1
    require(d_value[period] == 0, (p, "p delta((p+1)/4) is not a unit"))
    nu = pow(2, period, p) * d_unit[period] * pow(fact_unit[p + 1], -1, p) % p
    irregular = []
    for n in range(len(d)):
        m, r = 4 * n // (p + 1), residue(n, p)
        excess = d_value[n] - lower_bound(n, p)
        require(0 <= r < period and excess >= 0, (p, n, r, excess))
        require((excess == 0) == (r not in divisible_classes), (p, n, r, excess))
        left_unit = fact_unit[m] * pow(2, n, p) * d_unit[n] * pow(fact_unit[4 * n], -1, p) % p
        right_unit = pow(nu, m, p) * pow(2, r, p) * d_unit[r] * pow(fact_unit[4 * r], -1, p) % p
        require(residue_mod_p(excess, left_unit) == residue_mod_p(d_value[r], right_unit), (p, n, "congruence"))
        if excess != d_value[r]:
            irregular.append((n, excess))
    return divisible_classes, tuple(irregular)


def main() -> None:
    d_pickle, prime_bound = sys.argv[1], int(sys.argv[2])
    with open(d_pickle, "rb") as handle:
        d = tuple(pickle.load(handle))
    primes = primes_three_mod_four(prime_bound)
    results = {p: check_prime(d, p) for p in primes}
    exceptional = {p: classes for p, (classes, _) in results.items() if classes}
    print(f"Theorem 1.1 (i) and (ii), including the congruence, hold for n = 0..{len(d) - 1} and the {len(primes)} primes p = 3 (mod 4) below {prime_bound}")
    print(f"equality for every n: {len(primes) - len(exceptional)} primes; classes r with p | d(r) for the other {len(exceptional)}:")
    print("   " + ";  ".join(f"{p}: {', '.join(map(str, classes))}" for p, classes in exceptional.items()))
    irregular = {p: points for p, (_, points) in results.items() if points}
    print(f"points (n, excess) where the excess differs from v_p(d(r)): {irregular}")


if __name__ == "__main__":
    main()
