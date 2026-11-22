# Relation to earlier papers

For each earlier paper, the statements in it that this work proves, uses, sharpens or corrects.
Numbers on the left refer to the earlier paper; numbers on the right refer to
`paper/romik-valuation.tex`.

## C. Krattenthaler and T. W. Müller, arXiv:2304.11471

| Their statement | Here |
|---|---|
| Conjecture 45: for p ≡ 3 (mod 4), d(n) ≡ 0 (mod p^e) for n ≥ ⌈ep²/4⌉ | Proved (Corollary 1.2). It follows from the exact lower bound of Theorem 1.1(i). |
| Conjecture 43(1): p^(2e−1) divides u(n) for n ≥ ⌈(ep²−1)/2⌉, e ≥ 1 | Proved (Corollary 1.6(i)). The cases e ≤ 2 are in their Theorem 9; e ≥ 3 is new. Formalised in Lean from the recurrence (`conj43_one`). |
| Conjecture 43(2): p^(2e) divides u(n) for n ≥ (ep²+(e−2)p)/2, e ≥ 2 | Proved (Corollary 1.6(ii)). New for all e ≥ 2. Formalised in Lean from the recurrence (`conj43_two`). |
| Conjecture 43(2a): p² divides u(n) for n ≥ (p²−1)/2 | This is their Proposition 8. With the two rows above, every part of Conjecture 43 is proved. |
| Remark after Conjecture 43, (1): p divides u(n) for n ≥ (p²−p)/2 | Follows from their Lemma 7 and Proposition 8 (Corollary 1.6(iii)). |
| Remark after Conjecture 43, (2): p⁶ divides u(n) for n ≥ (3p²−1)/2 | Does not hold for p = 7, 11, 19, 23: v_p(u(n)) = 5 at n = (3p²+p−2)/2, for example v_7(u(76)) = 5 (Remark 6.4). |
| Conjecture 44(2): p^e divides v(n) for n ≥ ⌈ep²/4⌉, e even, "with very few exceptions" | One more exception: (p, e) = (3, 4), since v_3(v(10)) = 3 (Remark 6.4). Theorem 1.5 gives a general lower bound for v_p(v(n)); it does not prove Conjecture 44. |
| Their threshold ⌈(e−1)p²/2⌉ for d(n) ≡ 0 (mod p^e) | Replaced by the exact lower bound of Theorem 1.1. The threshold ⌈ep²/4⌉ of Conjecture 45 is sufficient but not always the least one: for p = 3, e = 4 the congruence holds from n = 7 on (Section 8.3). |

## D. Romik, Ramanujan J. 52 (2020), arXiv:1807.06130

| His statement | Here |
|---|---|
| Definition of d(n) | The object of the paper. |
| Section 8, Problem 2: congruences for d(n) modulo higher powers of primes | Theorem 1.1 gives, for p ≡ 3 (mod 4), a lower bound for v_p(d(n)) and the condition for equality. |
| Section 8, Problem 3: connections between such Taylor coefficients and other problems in number theory | Theorem 7.1: d(n)² is, up to an explicit factor, the central value L(ψ^(8n+1), 4n+1) for the Hecke character ψ of y² = x³ − x. |
| Theorem 7: the recursion v(n) = Σ r(n,k) d(k) | Used as an independent numerical check of Proposition 4.1 (`romik/recursion_check.py`). |

## K. Bannai, S. Kobayashi and S. Yasuda, Math. Z. 286 (2017)

| Their statement | Here |
|---|---|
| Corollary 5.5: bounds for the coefficients of the Weierstrass zeta function at supersingular primes | The main input for Theorems 1.1 and 1.4 (Theorem 3.1(c)). |
| Theorem 5.6: v_p(a_n) ≥ −τ_(n−1) for the coefficients of σ, with equality at n = p^k(p+1)+1 | Theorem 1.4: for y² = 4x³ − g₂x and p ≡ 3 (mod 4), a congruence for p^m m! a_n modulo p. Writing n − 1 = (p+1)m + s with 0 ≤ s ≤ p, equality holds if and only if a_(s+1) is a unit; in particular it holds for every n ≡ 1 (mod p+1). |
| Theorem 6.8: a lower bound for the p-adic valuation of critical values L(φ, 0) for Hecke characters of infinity type (a, −b), b > a ≥ 0, at inert primes p ≥ 5 | Corollary 7.2 treats the case φ = ψ^(8n+1) N^(−(4n+1)), (a, b) = (4n, 4n+1), with a sharper bound and the condition for equality. Example: for p = 7, n = 1 their bound is −209/48 and the value has valuation 0 (Section 7). |

## K. Nomoto, J. Number Theory 238 (2022)

| His statement | Here |
|---|---|
| Theorem 2.10: for the Hecke character of y² = x³ + x, L(ψ^(2k−1), k) is an explicit multiple of the squared absolute value of a derivative of θ₂ at τ = i | Theorem 7.1 is the corresponding statement for y² = x³ − x and θ₃, and its proof follows his. |

## F. Rodriguez Villegas and D. Zagier, Advances in Number Theory (1993)

| Their statement | Here |
|---|---|
| Formulas (9), (16) and the factorisation formula (23) | Used in the proof of Theorem 7.1 (Steps 2 and 4). |

## A. Burungale, S. Kobayashi and K. Ota, arXiv:2507.08221; with W. He, arXiv:2408.13932

| Their statement | Here |
|---|---|
| p-adic valuation of L(φχ, 1)/Ω at inert primes, for φ of infinity type (1, 0) and anticyclotomic characters χ of p-power order | A different family: in Corollary 7.2 the conductor is prime to p and the infinity type varies. |
| The case of general infinity type is mentioned as a natural problem (arXiv:2408.13932) | Corollary 7.2 concerns one family of characters of varying infinity type. |

## Earlier results on d(n) at p ≡ 3 (mod 4)

| Paper | Result | Here |
|---|---|---|
| R. Scherer, Ramanujan J. 54 (2021) | d(n) ≡ 0 (mod p) for n > (p²−1)/2 | Corollary 1.3: d(n) ≡ 0 (mod p) for n > (p²−1)/4, and p does not divide d((p²−1)/4). |
| J. Kim and Y. Lee, Taiwanese J. Math. 27 (2023); Krattenthaler–Müller | d(n) ≡ 0 (mod p^e) for n ≥ ⌈(e−1)p²/2⌉, e ≥ 2 | Corollary 1.2: n ≥ ⌈ep²/4⌉. |
