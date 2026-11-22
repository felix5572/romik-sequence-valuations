"""Romik's d(n) and central values of Hecke L-functions of Q(i).

Let psi be the Hecke character of Q(i) attached to E: y^2 = x^3 - x (conductor 32), and let
varpi = Gamma(1/4)^2 / (2 sqrt(2 pi)) be the lemniscate constant.  The script checks numerically

    L(psi^(8n+1), 4n+1) = varpi^(8n+1) / (pi^(4n) (4n)!) * 4^(n-1) * d(n)^2 .          (*)

The left side is the central value of the newform  sum_a psi(a)^(8n+1) q^N(a)  of weight 8n+2 and
level 32.  Its coefficients are built exactly from point counts of E modulo p, the functional
equation is checked numerically (this also gives the root number), and the central value is
computed from the standard rapidly convergent series.

Both sides of (*) are required to agree to a relative error below 10^-60 (working precision 110
digits).  For psi^(8n+5) the numerical functional-equation check gives the sign -1, which forces
the central value to vanish; this matches the vanishing of the odd Taylor coefficients of theta_3
at tau = i.  The sign is established here only numerically, for the exponents that are tested.

With `--other-curves` the same computation is done for y^2 = x^3 + x (level 64) and
y^2 = x^3 + 2x (level 256) and all exponents 4n+1; the normalised central values are again
squares of rationals, of other sequences.

Usage: python3 hecke_l_check.py <d_pickle> <max_n> [--other-curves]
"""
import pickle
import sys
from fractions import Fraction

from checks import require
from mpmath import exp, factorial, gamma, gammainc, mp, mpf, pi, sqrt

mp.dps = 110
TOLERANCE = mpf(10) ** (-60)  # every numerical identity below is required to this accuracy
COEFFICIENT_BOUND = 3000


def smallest_prime_factors(bound: int) -> tuple:
    spf = list(range(bound + 1))
    for p in range(2, int(bound**0.5) + 1):
        if spf[p] == p:
            for multiple in range(p * p, bound + 1, p):
                if spf[multiple] == multiple:
                    spf[multiple] = p
    return tuple(spf)


def trace_of_frobenius(D: int, p: int) -> int:
    """a_p of y^2 = x^3 - D x for an odd prime p."""
    half = (p - 1) // 2
    total = 0
    for x in range(p):
        value = (x * x * x - D * x) % p
        if value:
            total += 1 if pow(value, half, p) == 1 else -1
    return -total


def frobenius_element(D: int, p: int) -> complex:
    """pi in Z[i] with N(pi) = p and pi + conj(pi) = a_p, for p = 1 (mod 4); returned as (re, im)."""
    trace = trace_of_frobenius(D, p)
    require(trace % 2 == 0)
    real = trace // 2
    imaginary_squared = p - real * real
    imaginary = int(round(imaginary_squared**0.5))
    require(imaginary * imaginary == imaginary_squared, (D, p, trace))
    return (real, imaginary)


def gaussian_power(z: tuple, exponent: int) -> tuple:
    result = (1, 0)
    for _ in range(exponent):
        result = (result[0] * z[0] - result[1] * z[1], result[0] * z[1] + result[1] * z[0])
    return result


def prime_power_coefficients(D: int, p: int, k: int, bound: int) -> tuple:
    """Coefficients c(p^e), e >= 0, p^e <= bound, of the Euler factor of L(psi_D^k, s) at p."""
    exponents = range(1 + next(e for e in range(64) if p ** (e + 1) > bound))
    if p == 2:
        return tuple(1 if e == 0 else 0 for e in exponents)
    if p % 4 == 3:
        return tuple((-p) ** (k * e // 2) if e % 2 == 0 else 0 for e in exponents)
    root = gaussian_power(frobenius_element(D, p), k)
    trace, norm = 2 * root[0], p**k
    coefficients = [1, trace]
    for _ in exponents[2:]:
        coefficients.append(trace * coefficients[-1] - norm * coefficients[-2])
    return tuple(coefficients[: len(exponents)])


def dirichlet_coefficients(D: int, k: int, bound: int, spf: tuple) -> tuple:
    at_prime = {p: prime_power_coefficients(D, p, k, bound) for p in range(2, bound + 1) if spf[p] == p}
    coefficients = [0, 1]
    for m in range(2, bound + 1):
        p, rest, e = spf[m], m, 0
        while rest % p == 0:
            rest, e = rest // p, e + 1
        coefficients.append(at_prime[p][e] * coefficients[rest])
    return tuple(coefficients)


def root_number(coefficients: tuple, weight: int, level: int) -> int:
    """epsilon from F(1/t) = epsilon t^weight F(t), F(t) = sum c_m exp(-2 pi m t / sqrt(level))."""
    def F(t):
        return sum(c * exp(-2 * pi * m * t / sqrt(level)) for m, c in enumerate(coefficients) if c)

    t = mpf("1.15")
    ratio = F(1 / t) / (t**weight * F(t))
    sign = int(round(float(ratio)))
    require(sign in (1, -1) and abs(ratio - sign) < TOLERANCE, ratio)
    return sign


def central_value(coefficients: tuple, weight: int, level: int, sign: int):
    half = weight // 2
    return (1 + sign) * sum(
        c * mpf(m) ** (-half) * gammainc(half, 2 * pi * m / sqrt(level), regularized=True)
        for m, c in enumerate(coefficients)
        if c
    )


def lemniscate_constant():
    return gamma(mpf(1) / 4) ** 2 / (2 * sqrt(2 * pi))


def central_value_of_power(D: int, level: int, k: int, spf: tuple):
    """(root number, L(psi_D^k, (k+1)/2)) for odd k."""
    coefficients = dirichlet_coefficients(D, k, COEFFICIENT_BOUND, spf)
    sign = root_number(coefficients, k + 1, level)
    return sign, central_value(coefficients, k + 1, level, sign)


def check_romik_formula(d: tuple, max_n: int, spf: tuple) -> None:
    """Formula (*) of the module docstring, and the vanishing for the exponents 8n+5."""
    varpi = lemniscate_constant()
    print("== y^2 = x^3 - x, level 32:  L(psi^(8n+1), 4n+1)  against  varpi^(8n+1) 4^(n-1) d(n)^2 / (pi^(4n) (4n)!)")
    for n in range(max_n + 1):
        sign, value = central_value_of_power(1, 32, 8 * n + 1, spf)
        predicted = varpi ** (8 * n + 1) * mpf(4) ** (n - 1) * mpf(d[n]) ** 2 / (pi ** (4 * n) * factorial(4 * n))
        relative_error = abs(value / predicted - 1)
        odd_sign, _ = central_value_of_power(1, 32, 8 * n + 5, spf)
        require(sign == 1 and relative_error < TOLERANCE, (n, sign, relative_error))
        require(odd_sign == -1, (n, odd_sign))
        print(f"   n={n:2d}  L = {mp.nstr(value, 25)}  relative error {mp.nstr(relative_error, 3)};"
              f"  psi^({8 * n + 5}): root number {odd_sign:+d}")


HEIGHT_BOUND = 10**20  # a generic real number is within 10^-40, not 10^-60, of a fraction of this height


def square_root_fraction(value) -> str:
    """sqrt(value) as a fraction with denominator <= HEIGHT_BOUND, if it is one to within TOLERANCE."""
    root = sqrt(value)
    candidate = Fraction(mp.nstr(root, 80)).limit_denominator(HEIGHT_BOUND)
    error = abs(root - mpf(candidate.numerator) / candidate.denominator)
    return str(candidate) if error < TOLERANCE else f"not rational ({mp.nstr(root, 12)})"


def report_other_curve(D: int, level: int, max_n: int, spf: tuple) -> None:
    """sqrt of  L(psi_D^(4n+1), 2n+1) pi^(2n) (2n)! / varpi^(4n+1), relative to n = 0."""
    varpi = lemniscate_constant()
    values = tuple(
        central_value_of_power(D, level, 4 * n + 1, spf)[1] * pi ** (2 * n) * factorial(2 * n) / varpi ** (4 * n + 1)
        for n in range(max_n + 1)
    )
    print(f"== y^2 = x^3 - ({D}) x, level {level}: sqrt of normalised L(psi^(4n+1), 2n+1), relative to n = 0")
    print("   " + ", ".join(square_root_fraction(value / values[0]) for value in values))


def main() -> None:
    d_pickle, max_n = sys.argv[1], int(sys.argv[2])
    with open(d_pickle, "rb") as handle:
        d = tuple(pickle.load(handle))
    spf = smallest_prime_factors(COEFFICIENT_BOUND)
    check_romik_formula(d, max_n, spf)
    if "--other-curves" in sys.argv[3:]:
        for D, level in ((-1, 64), (-2, 256)):
            report_other_curve(D, level, 2 * max_n, spf)


if __name__ == "__main__":
    main()
