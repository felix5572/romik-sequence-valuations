"""Check d(n) against Romik's recursive characterisation (Romik, Theorem 7; Krattenthaler-Mueller, Section 2).

With u(n), v(n) from uv.py and  U(t) = sum_n u(n) t^(2n+1) / (2n+1)!,

    r(n, k) = 2^(n-k) (2n)!/(2k)! [t^(2n)] U(t)^(2k),        v(n) = sum_{k<=n} r(n, k) d(k).

Since r(n, n) = 1 this determines d(n) from d(0..n-1).  The script solves the recursion and compares
with the pickled values.  Those were computed by romik.py, from an integer ODE system for the
derivatives of theta_3 at tau = i in the Cayley variable; lean_hypotheses_check.py checks separately
that the same values are the Taylor coefficients of sigma(z) sqrt(wp(z)).  So this script ties the
data to the published recursive description of the sequence, independently of both.

Usage: python3 recursion_check.py <d_pickle> <max_n>
"""
import pickle
import sys
from fractions import Fraction as Fr
from math import factorial

from checks import require
from uv import squared_products, u_sequence, v_sequence

Series = tuple  # index j <-> coefficient of x^j, x = t^2


def truncated_product(a: Series, b: Series) -> Series:
    return tuple(sum(a[i] * b[n - i] for i in range(n + 1)) for n in range(len(a)))


def powers_of_u_squared(u: tuple, max_n: int) -> tuple:
    """W^k for k = 0..max_n, where U(t)^2 = t^2 W(t^2), truncated after x^max_n."""
    base = tuple(Fr(int(u[n]), factorial(2 * n + 1)) for n in range(max_n + 1))
    w = truncated_product(base, base)
    powers = [(Fr(1),) + (Fr(0),) * max_n]
    for _ in range(max_n):
        powers.append(truncated_product(powers[-1], w))
    return tuple(powers)


def r_entry(powers: tuple, n: int, k: int) -> int:
    """r(n, k) = 2^(n-k) (2n)!/(2k)! [x^(n-k)] W^k."""
    value = Fr(2 ** (n - k) * factorial(2 * n), factorial(2 * k)) * powers[k][n - k]
    require(value.denominator == 1, (n, k))
    return value.numerator


def solve_recursion(v: tuple, powers: tuple, max_n: int) -> tuple:
    d = []
    for n in range(max_n + 1):
        require(r_entry(powers, n, n) == 1)
        d.append(int(v[n]) - sum(r_entry(powers, n, k) * d[k] for k in range(n)))
    return tuple(d)


def main() -> None:
    d_pickle, max_n = sys.argv[1], int(sys.argv[2])
    with open(d_pickle, "rb") as handle:
        expected = tuple(pickle.load(handle))[: max_n + 1]
    pi1, pi3 = squared_products(max_n, 1), squared_products(max_n, 3)
    u, v = u_sequence(max_n, pi1, pi3), v_sequence(max_n, pi3)
    d = solve_recursion(v, powers_of_u_squared(u, max_n), max_n)
    mismatches = tuple(n for n in range(max_n + 1) if d[n] != expected[n])
    require(not mismatches, mismatches[:5])
    print(f"Romik's recursion reproduces d(n) for n = 0..{max_n}; d(0..6) = {d[:7]}")


main()
