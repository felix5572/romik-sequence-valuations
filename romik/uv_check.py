"""Checks for the bounds on Romik's auxiliary sequences u(n), v(n) at primes p = 3 (mod 4).

    v_p(u(n)) >= v_p((2n+1)!) - floor((2n+1)/(p+1))
    v_p(v(n)) >= v_p((2n)!)   - floor(2n/(p+1))

1. the two bounds on the data;
2. the explicit series  sum Pi3(j) t^(2j)/(2j)!  and  sum Pi1(n) t^(2n+1)/(2n+1)!  have
   coefficients of valuation >= -floor(degree/(p+1));
3. with B(k) = v_p(k!) - floor(k/(p+1)):  B(k) >= 2e-1 for k >= e p^2,  B(k) >= 2e for odd
   k >= e p^2 + (e-2) p + 1 (e >= 2),  B(k) >= 1 for odd k >= p^2 - p + 1.  These give parts
   (1), (2), (2a) of Conjecture 43 of Krattenthaler-Mueller;
4. for p = 1 (mod 4):  v_p(v(n)) >= v_p((2n)!).

usage: python3 uv_check.py UV_PICKLE PRIME_LIMIT
"""
import pickle
import sys

from checks import require
from lower_bound_check import vp_factorial, vp_int


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % q for q in range(2, int(n**0.5) + 1))


def bound(k: int, p: int) -> int:
    """B(k) = v_p(k!) - floor(k/(p+1))."""
    return vp_factorial(k, p) - k // (p + 1)


def data_violations(sequence: list, degree, p: int) -> tuple:
    return tuple(n for n, x in enumerate(sequence) if vp_int(x, p) < bound(degree(n), p))


def explicit_series_violations(p: int, count: int) -> tuple:
    """Pi3(j)/(2j)! and Pi1(j)/(2j+1)! against -floor(degree/(p+1))."""
    out = []
    v_pi3, v_pi1 = 0, 0
    for j in range(1, count + 1):
        v_pi3 += 2 * vp_int(4 * j - 3, p)
        v_pi1 += 2 * vp_int(4 * j - 1, p)
        if v_pi3 - vp_factorial(2 * j, p) < -((2 * j) // (p + 1)):
            out.append(("Pi3", j))
        if v_pi1 - vp_factorial(2 * j + 1, p) < -((2 * j + 1) // (p + 1)):
            out.append(("Pi1", j))
    return tuple(out)


def threshold_violations(p: int, max_e: int) -> tuple:
    out = []
    window = 6 * p * p
    if any(bound(k, p) < 1 for k in range(p * p - p + 1, p * p - p + 1 + window, 2)):
        out.append(("mod p", 1))
    for e in range(1, max_e + 1):
        start = e * p * p
        if any(bound(k, p) < 2 * e - 1 for k in range(start, start + window)):
            out.append(("43(1)", e))
        start_even = e * p * p + (e - 2) * p + 1
        if e >= 2 and any(bound(k, p) < 2 * e for k in range(start_even, start_even + window, 2)):
            out.append(("43(2)", e))
    return tuple(out)


def main() -> None:
    uv_pickle, prime_limit = sys.argv[1], int(sys.argv[2])
    with open(uv_pickle, "rb") as handle:
        data = pickle.load(handle)
    u, v = data["u"], data["v"]
    inert = tuple(p for p in range(3, prime_limit) if p % 4 == 3 and is_prime(p))
    split = tuple(p for p in range(5, prime_limit) if p % 4 == 1 and is_prime(p))
    print(f"n <= {len(u) - 1}; {len(inert)} primes p = 3 (mod 4) below {prime_limit}")
    bad_u = {p: data_violations(u, lambda n: 2 * n + 1, p)[:3] for p in inert}
    bad_v = {p: data_violations(v, lambda n: 2 * n, p)[:3] for p in inert}
    print(" 1 bound for u violated at:", {p: b for p, b in bad_u.items() if b})
    print(" 1 bound for v violated at:", {p: b for p, b in bad_v.items() if b})
    tight_u = {p: sum(1 for n, x in enumerate(u) if vp_int(x, p) == bound(2 * n + 1, p)) for p in inert[:4]}
    print(" 1 number of n with equality for u:", tight_u)
    bad_series = {p: explicit_series_violations(p, 6000)[:3] for p in inert}
    print(" 2 explicit series violations:", {p: b for p, b in bad_series.items() if b})
    bad_thresholds = {p: threshold_violations(p, 60)[:3] for p in inert}
    print(" 3 threshold violations (e <= 60):", {p: b for p, b in bad_thresholds.items() if b})
    bad_split = {p: tuple(n for n, x in enumerate(v) if vp_int(x, p) < vp_factorial(2 * n, p))[:3] for p in split}
    print(" 4 p = 1 (mod 4), v_p(v(n)) >= v_p((2n)!) violated at:", {p: b for p, b in bad_split.items() if b})
    checks = (("u", bad_u), ("v", bad_v), ("series", bad_series), ("thresholds", bad_thresholds), ("split", bad_split))
    for name, bad in checks:
        require(not any(bad.values()), (name, {p: b for p, b in bad.items() if b}))


if __name__ == "__main__":
    main()
