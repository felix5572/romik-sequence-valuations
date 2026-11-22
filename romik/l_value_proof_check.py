"""Numerical check of every step in the proof of the L-value formula (Section 7 of the paper).

Notation: psi is the Hecke character of y^2 = x^3 - x, h >= 0, p = 2h, and

    theta_p   = i^(-p) (2 pi)^(-p/2) sum_n H_p(n sqrt(2 pi)) exp(-pi n^2)        (= theta_(p)[0,0](i))
    S_p       = sum_{n,m} (-1)^(nm) L_p(pi (n^2 + m^2)) exp(-pi (n^2 + m^2) / 2)
    DTheta(y) = d_1^(p) Theta at z = i y,  Theta(z) = sum_{n,m} q^(n^2 + m^2),
              = p! / (4 pi y)^p * sum_{n,m} L_p(4 pi (n^2 + m^2) y) exp(-2 pi (n^2 + m^2) y)

Steps checked, each to a relative error below 10^-60:

  A. factorisation formula of Rodriguez Villegas and Zagier:   p!/pi^p S_p = sqrt(2) theta_p^2
  B. S_p = pi^p/p! (DTheta(1/4) - 2^(p+1) DTheta(1/2) + 2^(2p+1) DTheta(1))
  C. Eisenstein side:  L(psi^(4h+1), 2h+1) = pi^(p+1)/(2 p!) (4^p DTheta(1) - 2^(p-1) DTheta(1/2))
  D. Fricke involution:  DTheta(1/4) = 2^(2p+1) DTheta(1)
  E. for h = 2n:  theta_(4n) = theta_3(1) d(n) (4 Phi / pi^2)^n
  F. conclusion:  sqrt(2) theta_p^2 = 8 p!/pi^(p+1) L(psi^(4h+1), 2h+1)   (both sides vanish for odd h)

Usage: python3 l_value_proof_check.py <d_pickle> <max_h>
"""
import pickle
import sys

from mpmath import exp, factorial, gamma, hermite, laguerre, mp, mpf, pi, sqrt

from checks import require
from hecke_l_check import COEFFICIENT_BOUND, TOLERANCE, central_value_of_power, smallest_prime_factors

RADIUS = 24  # lattice points with |n|, |m| <= RADIUS; the neglected tail is far below TOLERANCE


def lattice_norm_counts() -> dict:
    """{N: (number of (n, m) with n^2 + m^2 = N, number of those with n m odd)}."""
    counts = {}
    for n in range(-RADIUS, RADIUS + 1):
        for m in range(-RADIUS, RADIUS + 1):
            total, odd = counts.get(n * n + m * m, (0, 0))
            counts[n * n + m * m] = (total + 1, odd + (n * m) % 2)
    return counts


def theta_hermite(p: int):
    total = sum(hermite(p, n * sqrt(2 * pi)) * exp(-pi * n * n) for n in range(-RADIUS, RADIUS + 1))
    return mpf(-1) ** (p // 2) * (2 * pi) ** (-mpf(p) / 2) * total


def signed_laguerre_sum(p: int, counts: dict):
    return sum((total - 2 * odd) * laguerre(p, 0, pi * N) * exp(-pi * N / 2) for N, (total, odd) in counts.items())


def shimura_derivative_of_theta(p: int, y, counts: dict):
    series = sum(total * laguerre(p, 0, 4 * pi * N * y) * exp(-2 * pi * N * y) for N, (total, _) in counts.items())
    return factorial(p) / (4 * pi * y) ** p * series


def close(a, b) -> bool:
    scale = max(abs(a), abs(b))
    return abs(a - b) <= TOLERANCE * scale if scale > mpf(10) ** (-40) else abs(a - b) < TOLERANCE


def check_h(h: int, d: tuple, counts: dict, spf: tuple) -> None:
    p = 2 * h
    theta_p = theta_hermite(p)
    S = signed_laguerre_sum(p, counts)
    quarter, half, one = (shimura_derivative_of_theta(p, mpf(y), counts) for y in ("0.25", "0.5", "1"))
    sign, L = central_value_of_power(1, 32, 4 * h + 1, spf)
    left = sqrt(2) * theta_p**2
    require(close(factorial(p) / pi**p * S, left), ("A", h))
    require(close(S, pi**p / factorial(p) * (quarter - 2 ** (p + 1) * half + 2 ** (2 * p + 1) * one)), ("B", h))
    require(close(L, pi ** (p + 1) / (2 * factorial(p)) * (4**p * one - 2 ** (p - 1) * half)), ("C", h))
    require(close(quarter, 2 ** (2 * p + 1) * one), ("D", h))
    if h % 2 == 0:
        n = h // 2
        theta3_at_1 = pi ** mpf("0.25") / gamma(mpf("0.75"))
        Phi = gamma(mpf("0.25")) ** 8 / (128 * pi**4)
        require(close(theta_p, theta3_at_1 * d[n] * (4 * Phi / pi**2) ** n), ("E", h))
    require(close(left, 8 * factorial(p) / pi ** (p + 1) * L), ("F", h))
    print(f"   h={h:2d}: steps A-F hold; root number {sign:+d}, L(psi^({4 * h + 1}), {2 * h + 1}) = {mp.nstr(L, 20)}")


def main() -> None:
    d_pickle, max_h = sys.argv[1], int(sys.argv[2])
    with open(d_pickle, "rb") as handle:
        d = tuple(pickle.load(handle))
    counts, spf = lattice_norm_counts(), smallest_prime_factors(COEFFICIENT_BOUND)
    print("== proof of the L-value formula, step by step")
    for h in range(max_h + 1):
        check_h(h, d, counts, spf)


if __name__ == "__main__":
    main()
