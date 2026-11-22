"""Check the hypotheses of the Lean theorem `Romik.romik_main` on the actual lemniscatic data.

`lean/Romik/Theta.lean` proves Theorem 1.1 for any b, f, w, d satisfying a list of hypotheses.
Here b, f, w are built exactly as the Lean statement characterises them (g2 = 4, g3 = 0):

    zeta(z) = 1/z + sum b_n z^n,   f' = (sum b_n z^n) f,  f(0) = 1,
    w^2 = 1 - z^2 (sum b_n z^n)',  w(0) = 1,

and every hypothesis is asserted, for each prime p = 3 (mod 4) below `max_degree`:

    hsupp  : b_n = 0 unless n = 3 (mod 4)
    hsmall : v_p(b_n) >= 0                               for n < p
    hall   : v_p(b_n) >= -1 - floor((n - p)/(p^2 - 1))   for n >= p
    hcop   : v_p(b_n) >= -floor((n + 1)/(p^2 - 1))       if p does not divide n
    hunit  : v_p(b_p) = -1
    hd     : d(k) = (4k)!/2^k [z^(4k)] (f w)             (independent of p)

Usage: python3 lean_hypotheses_check.py <max_degree> <d_pickle>
"""
import pickle
import sys
from fractions import Fraction as Fr
from math import factorial

from checks import require
from lower_bound_check import LEMNISCATIC, vp, wp_series

Series = tuple  # index n <-> coefficient of z^n


def zeta_coefficients(max_degree: int) -> Series:
    """b_n for 0 <= n <= max_degree: zeta = 1/z - sum_{k>=2} c_k z^(2k-1)/(2k-1)."""
    wp = wp_series(LEMNISCATIC, max_degree // 2 + 1)
    return tuple(
        -wp[(n + 1) // 2] / n if n % 2 == 1 and n >= 3 else Fr(0) for n in range(max_degree + 1)
    )


def solve_log_derivative(b: Series) -> Series:
    """f with f(0) = 1 and f' = (sum b_n z^n) f:  (n+1) f_(n+1) = sum_k b_k f_(n-k)."""
    support = tuple(k for k, value in enumerate(b) if value != 0)
    f = [Fr(1)]
    for n in range(len(b) - 1):
        f.append(sum((b[k] * f[n - k] for k in support if k <= n), Fr(0)) / (n + 1))
    return tuple(f)


def wp_times_z_squared(b: Series) -> Series:
    """1 - z^2 (sum b_n z^n)': the coefficient of z^n is -(n-1) b_(n-1) for n >= 2."""
    return (Fr(1), Fr(0)) + tuple(-(n - 1) * b[n - 1] for n in range(2, len(b)))


def square_root(g: Series) -> Series:
    """w with w(0) = 1 and w^2 = g."""
    require(g[0] == 1)
    w = [Fr(1)]
    for n in range(1, len(g)):
        w.append((g[n] - sum((w[k] * w[n - k] for k in range(1, n) if w[k] != 0), Fr(0))) / 2)
    return tuple(w)


def product(a: Series, b: Series) -> Series:
    support = tuple(j for j, value in enumerate(b) if value != 0)
    return tuple(sum((a[n - j] * b[j] for j in support if j <= n), Fr(0)) for n in range(len(a)))


def check_support(b: Series) -> None:
    require(all(value == 0 for n, value in enumerate(b) if n % 4 != 3))


def check_bky_bounds(b: Series, p: int) -> None:
    nonzero = tuple((n, vp(value, p)) for n, value in enumerate(b) if value != 0)
    require(all(v >= 0 for n, v in nonzero if n < p))
    require(all(v >= -1 - (n - p) // (p * p - 1) for n, v in nonzero if n >= p))
    require(all(v >= -((n + 1) // (p * p - 1)) for n, v in nonzero if n % p != 0))
    require(vp(b[p], p) == -1)


def check_identification(theta: Series, d: tuple) -> int:
    count = min(len(d), len(theta) // 4)
    require(all(d[k] == Fr(factorial(4 * k), 2**k) * theta[4 * k] for k in range(count)))
    return count


def primes_three_mod_four(limit: int) -> tuple:
    return tuple(
        p for p in range(3, limit, 4) if all(p % q != 0 for q in range(3, int(p**0.5) + 1, 2))
    )


def main() -> None:
    max_degree, d_pickle = int(sys.argv[1]), sys.argv[2]
    with open(d_pickle, "rb") as handle:
        d = tuple(pickle.load(handle))
    b = zeta_coefficients(max_degree)
    check_support(b)
    theta = product(solve_log_derivative(b), square_root(wp_times_z_squared(b)))
    count = check_identification(theta, d)
    print(f"hsupp ok to degree {max_degree}; hd ok for k = 0..{count - 1}")
    primes = primes_three_mod_four(max_degree)
    for p in primes:
        check_bky_bounds(b, p)
    print(f"hsmall, hall, hcop, hunit ok to degree {max_degree} for p in {primes}")


main()
