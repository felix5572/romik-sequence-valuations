"""Romik's auxiliary sequences u(n), v(n) (Krattenthaler-Mueller, arXiv:2304.11471, Section 2).

    u(n) = Pi1(n) - sum_{m<n} C(2n+1, 2m+1) Pi3(n-m) u(m),              u(0) = 1
    v(n) = 2^(n-1) Pi3(n) - (1/2) sum_{0<m<n} C(2n, 2m) v(m) v(n-m),    v(0) = 1
    Pi1(N) = prod_{j<=N} (4j-1)^2,  Pi3(N) = prod_{j<=N} (4j-3)^2

usage: python3 uv.py N OUT_PICKLE     -> pickles {"u": [...], "v": [...]} for n = 0..N
"""
import pickle
import sys
from math import comb

from checks import require
from gmpy2 import mpz

KNOWN_U = (1, 6, 256, 28560, 6071040, 2098483200, 1071889920000)
KNOWN_V = (1, 1, 47, 7395, 2453425, 1399055625, 1221037941375)


def squared_products(count: int, offset: int) -> tuple:
    """(prod_{j<=N} (4j-offset)^2) for N = 0..count."""
    out = [mpz(1)]
    for j in range(1, count + 1):
        out.append(out[-1] * (4 * j - offset) ** 2)
    return tuple(out)


def u_sequence(count: int, pi1: tuple, pi3: tuple) -> tuple:
    u = [mpz(1)]
    for n in range(1, count + 1):
        correction = sum(comb(2 * n + 1, 2 * m + 1) * pi3[n - m] * u[m] for m in range(n))
        u.append(pi1[n] - correction)
    return tuple(u)


def v_sequence(count: int, pi3: tuple) -> tuple:
    v = [mpz(1), mpz(1)]
    for n in range(2, count + 1):
        correction = sum(comb(2 * n, 2 * m) * v[m] * v[n - m] for m in range(1, n))
        require(correction % 2 == 0)
        v.append(mpz(2) ** (n - 1) * pi3[n] - correction // 2)
    return tuple(v[: count + 1])


def main() -> None:
    count, out = int(sys.argv[1]), sys.argv[2]
    pi1, pi3 = squared_products(count, 1), squared_products(count, 3)
    u, v = u_sequence(count, pi1, pi3), v_sequence(count, pi3)
    require(tuple(u[: len(KNOWN_U)]) == KNOWN_U, u[:7])
    require(tuple(v[: len(KNOWN_V)]) == KNOWN_V, v[:7])
    with open(out, "wb") as handle:
        pickle.dump({"u": [int(x) for x in u], "v": [int(x) for x in v]}, handle)
    print(f"u, v computed for n = 0..{count}; first values match the published ones")


if __name__ == "__main__":
    main()
