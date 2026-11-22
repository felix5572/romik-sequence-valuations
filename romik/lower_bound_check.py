"""Numerical checks for a proof route to the lower bound  v_p(c_A) >= v_p(A!) - v_p((p*floor(A/(p+1)))!).

Notation: p is a prime of supersingular reduction, n is a degree in z, beta(n) = v_p((p*floor(n/(p+1)))!).
D is the ring of power series sum a_n z^n with v_p(a_n) >= -beta(n); the lower bound says sigma(z)/z is in D.

Route (each link is checked below on exact rationals):
  1. weight:   z^2 wp(z) = sum c_k z^(2k)  has  v_p(c_k) >= -floor(2k/(p^2-1)).
  2. integers: with l_n = [z^n] log(sigma(z)/z) = -c_(n/2)/(n(n-1)), link 1 gives v_p(l_n) >= -a(n),
               a(n) = floor(n/(p^2-1)) + v_p(n) + v_p(n-1); need a(n) <= beta(n) and 1 + a(n/p) <= beta(n).
  3. defect:   N(z) = L(z) - L(z^p)/p lies in D, L = log(sigma(z)/z).  By Dwork's lemma this is
               equivalent to sigma(z)/z in D.
  4. members:  sigma(z)/z and theta(z) = sigma(z) sqrt(wp(z)) lie in D; count where the bound is attained.
  5. romik:    d(n) = kappa^n * (4n)! [z^(4n)] sigma(z) sqrt(wp(z)) on the lattice g2 = 4, g3 = 0.
  6. equality: past degree p+1 the defect N lies in p*D, so f = V(z) exp(u y) (1 + p*J) with V integral,
               y = z^(p+1)/p; hence  p^m m! f_((p+1)m+r) = (p f_(p+1))^m f_r (mod p), and the bound is
               attained at degree (p+1)m+r exactly when f_r is a unit.

The paper (paper/romik-valuation.tex) no longer uses Dwork's lemma: links 3 and 6 are replaced by the
direct factorisation of Proposition 2.4.  The checks below are kept as independent numerical evidence.

usage: python3 lower_bound_check.py MAX_DEGREE INTEGER_CHECK_LIMIT D_PICKLE
"""
import pickle
import sys
from dataclasses import dataclass
from fractions import Fraction as Fr
from math import factorial
from checks import require

Series = tuple  # coefficients in u = z^2, index k <-> degree 2k in z


@dataclass(frozen=True)
class Lattice:
    name: str
    g2: Fr
    g3: Fr
    degree_step: int      # sigma(z)/z is a series in z^degree_step
    primes: tuple         # primes of supersingular reduction to test


LEMNISCATIC = Lattice("lemniscatic g2=4 g3=0", Fr(4), Fr(0), 4, (3, 7, 11, 19, 23, 31, 43))
EQUIANHARMONIC = Lattice("equianharmonic g2=0 g3=4", Fr(0), Fr(4), 6, (5, 11, 17, 23, 29, 41))


def vp_int(n: int, p: int) -> int:
    require(n != 0)
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def vp(x: Fr, p: int) -> int:
    return vp_int(x.numerator, p) - vp_int(x.denominator, p)


def vp_factorial(n: int, p: int) -> int:
    total = 0
    while n:
        n //= p
        total += n
    return total


def beta(n: int, p: int) -> int:
    return vp_factorial(p * (n // (p + 1)), p)


def wp_series(lattice: Lattice, top: int) -> Series:
    """z^2 wp(z) = 1 + sum_{k>=2} c_k u^k, by the standard recursion for the coefficients of wp."""
    c = [Fr(0)] * (top + 1)
    c[0] = Fr(1)
    if top >= 2:
        c[2] = lattice.g2 / 20
    if top >= 3:
        c[3] = lattice.g3 / 28
    for k in range(4, top + 1):
        c[k] = Fr(3, (2 * k + 1) * (k - 3)) * sum(c[m] * c[k - m] for m in range(2, k - 1))
    return tuple(c)


def log_sigma_series(wp: Series) -> Series:
    """L(u) = log(sigma(z)/z) = -sum c_k u^k / ((2k-1) 2k)."""
    return (Fr(0), Fr(0)) + tuple(-wp[k] / ((2 * k - 1) * (2 * k)) for k in range(2, len(wp)))


def series_exp(log_series: Series) -> Series:
    """E = exp(L) from n E_n = sum_k k L_k E_(n-k)."""
    support = tuple(k for k, value in enumerate(log_series) if value != 0)
    out = [Fr(1)]
    for n in range(1, len(log_series)):
        out.append(sum((k * log_series[k] * out[n - k] for k in support if k <= n), Fr(0)) / n)
    return tuple(out)


def series_sqrt(series: Series) -> Series:
    require(series[0] == 1)
    out = [Fr(1)]
    for n in range(1, len(series)):
        out.append((series[n] - sum((out[k] * out[n - k] for k in range(1, n)), Fr(0))) / 2)
    return tuple(out)


def series_mul(a: Series, b: Series) -> Series:
    support_b = tuple(j for j, value in enumerate(b) if value != 0)
    return tuple(sum((a[n - j] * b[j] for j in support_b if j <= n), Fr(0)) for n in range(len(a)))


def dwork_defect(log_series: Series, p: int) -> Series:
    """N(z) = L(z) - L(z^p)/p; the substitution z -> z^p is u -> u^p."""
    return tuple(
        value - (log_series[k // p] / p if k % p == 0 else 0) for k, value in enumerate(log_series)
    )


def slack_summary(slacks: tuple) -> str:
    """slacks: (degree, slack) pairs; slack >= 0 means the bound holds, 0 means it is attained."""
    worst = min(slacks, key=lambda pair: pair[1])
    tight = sum(1 for _, slack in slacks if slack == 0)
    verdict = "ok" if worst[1] >= 0 else "FAIL"
    return f"{verdict}  min slack {worst[1]} at degree {worst[0]}, attained at {tight}/{len(slacks)} degrees"


def check_weight(wp: Series, p: int) -> str:
    slacks = tuple(
        (2 * k, vp(c, p) + (2 * k) // (p * p - 1)) for k, c in enumerate(wp) if k >= 2 and c != 0
    )
    return slack_summary(slacks)


def check_in_ring(series: Series, p: int) -> str:
    slacks = tuple((2 * k, vp(x, p) + beta(2 * k, p)) for k, x in enumerate(series) if k >= 1 and x != 0)
    return slack_summary(slacks)


def check_defect_strict(defect: Series, p: int) -> str:
    """Beyond degree p+1 the Dwork defect should lie in p*D, i.e. slack >= 1."""
    slacks = tuple(
        (2 * k, vp(x, p) + beta(2 * k, p)) for k, x in enumerate(defect) if 2 * k > p + 1 and x != 0
    )
    worst = min(slacks, key=lambda pair: pair[1])
    verdict = "ok" if worst[1] >= 1 else "FAIL"
    return f"{verdict}  min slack {worst[1]} at degree {worst[0]} over {len(slacks)} degrees"


def check_leading_congruence(series: Series, p: int) -> str:
    """p^m m! f_((p+1)m+r) = (p f_(p+1))^m f_r  (mod p)  for 0 <= r <= p.

    This says the coefficient of z^r y^m/m!, y = z^(p+1)/p, is u^m f_r modulo p with u = p f_(p+1);
    it gives: the lower bound is attained at degree (p+1)m+r exactly when f_r is a p-adic unit.
    """
    unit = p * series[(p + 1) // 2]
    failures = []
    for k, coefficient in enumerate(series):
        m, r = divmod(2 * k, p + 1)
        difference = p**m * factorial(m) * coefficient - unit**m * series[r // 2]
        if difference != 0 and vp(difference, p) < 1:
            failures.append(2 * k)
    verdict = "ok" if not failures else "FAIL"
    return f"{verdict}  v_p(u) = {vp(unit, p)}, {len(failures)} failures over {len(series)} degrees {failures[:6]}"


def log_coefficient_bound(n: int, p: int) -> int:
    """a(n): link 1 gives v_p(l_n) >= -a(n)."""
    return n // (p * p - 1) + vp_int(n, p) + vp_int(n - 1, p)


def integer_inequality_failures(lattice: Lattice, p: int, limit: int) -> tuple:
    step = lattice.degree_step
    direct = tuple(
        ("direct", n) for n in range(step, limit + 1, step) if log_coefficient_bound(n, p) > beta(n, p)
    )
    frobenius = tuple(
        ("frobenius", n)
        for n in range(step * p, limit + 1, step * p)
        if 1 + log_coefficient_bound(n // p, p) > beta(n, p)
    )
    return direct + frobenius


def check_lattice(lattice: Lattice, max_degree: int, integer_limit: int) -> None:
    top = max_degree // 2
    wp = wp_series(lattice, top)
    log_sigma = log_sigma_series(wp)
    sigma_over_z = series_exp(log_sigma)
    theta = series_mul(sigma_over_z, series_sqrt(wp))
    print(f"== {lattice.name}, degrees up to {2 * top}")
    for p in lattice.primes:
        failures = integer_inequality_failures(lattice, p, integer_limit)
        print(f" p={p}")
        print(f"   1 weight of z^2 wp        : {check_weight(wp, p)}")
        print(f"   2 integer inequalities    : {len(failures)} failures up to {integer_limit} {failures[:6]}")
        print(f"   3 Dwork defect in D       : {check_in_ring(dwork_defect(log_sigma, p), p)}")
        print(f"   4 sigma/z in D            : {check_in_ring(sigma_over_z, p)}")
        print(f"   4 sigma*sqrt(wp) in D     : {check_in_ring(theta, p)}")
        print(f"   6 defect in p*D past p+1  : {check_defect_strict(dwork_defect(log_sigma, p), p)}")
        print(f"   6 leading term, sigma/z   : {check_leading_congruence(sigma_over_z, p)}")
        print(f"   6 leading term, theta     : {check_leading_congruence(theta, p)}")


def check_romik_identification(d_pickle: str, max_degree: int) -> None:
    """Romik's d(n) against (4n)! [z^(4n)] sigma(z) sqrt(wp(z)) on the lemniscatic lattice."""
    with open(d_pickle, "rb") as handle:
        d = pickle.load(handle)
    top = max_degree // 2
    wp = wp_series(LEMNISCATIC, top)
    theta = series_mul(series_exp(log_sigma_series(wp)), series_sqrt(wp))
    count = min(len(d) - 1, top // 2)
    ratios = tuple(Fr(d[n]) / (theta[2 * n] * factorial(4 * n)) for n in range(1, count + 1))
    kappa = ratios[0]
    mismatches = tuple(n for n, ratio in enumerate(ratios, start=1) if ratio != kappa**n)
    print(f"== Romik identification: d(n) = kappa^n (4n)! [z^(4n)] sigma sqrt(wp), kappa = {kappa}")
    print(f"   checked n = 1..{count}: {len(mismatches)} mismatches {mismatches[:6]}")
    if mismatches:
        print("   first ratios:", [str(r) for r in ratios[:6]])


def main() -> None:
    max_degree, integer_limit, d_pickle = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    check_romik_identification(d_pickle, max_degree)
    check_lattice(LEMNISCATIC, max_degree, integer_limit)
    check_lattice(EQUIANHARMONIC, max_degree, integer_limit)


if __name__ == "__main__":
    main()
