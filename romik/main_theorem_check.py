"""Check Theorem 1.1 of the paper on the computed values of Romik's sequence d(n).

For every prime p = 3 (mod 4) below `prime_bound` and every n in the data, with A = 4n,
m = floor(A/(p+1)) and r = n - m(p+1)/4, the script requires

    (i)   v_p(d(n)) >= v_p(A!) - v_p((p m)!),
    (ii)  equality holds if and only if p does not divide d(r),

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


def check_prime(d: tuple, p: int) -> tuple:
    """(residue classes r with p | d(r), points where the excess differs from v_p(d(r)))."""
    period = (p + 1) // 4
    divisible_classes = tuple(r for r in range(min(period, len(d))) if d[r] % p == 0)
    irregular = []
    for n in range(len(d)):
        excess = valuation(d[n], p) - lower_bound(n, p)
        r = residue(n, p)
        require(0 <= r < period and excess >= 0, (p, n, r, excess))
        require((excess == 0) == (r not in divisible_classes), (p, n, r, excess))
        if excess != valuation(d[r], p):
            irregular.append((n, excess))
    return divisible_classes, tuple(irregular)


def main() -> None:
    d_pickle, prime_bound = sys.argv[1], int(sys.argv[2])
    with open(d_pickle, "rb") as handle:
        d = tuple(pickle.load(handle))
    primes = primes_three_mod_four(prime_bound)
    results = {p: check_prime(d, p) for p in primes}
    exceptional = {p: classes for p, (classes, _) in results.items() if classes}
    print(f"Theorem 1.1 (i) and (ii) hold for n = 0..{len(d) - 1} and the {len(primes)} primes p = 3 (mod 4) below {prime_bound}")
    print(f"equality for every n: {len(primes) - len(exceptional)} primes; classes r with p | d(r) for the other {len(exceptional)}:")
    print("   " + ";  ".join(f"{p}: {', '.join(map(str, classes))}" for p, classes in exceptional.items()))
    irregular = {p: points for p, (_, points) in results.items() if points}
    print(f"points (n, excess) where the excess differs from v_p(d(r)): {irregular}")


if __name__ == "__main__":
    main()
