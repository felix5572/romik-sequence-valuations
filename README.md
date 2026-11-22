# Valuations of Romik's sequence

Paper draft, numerical checks and a Lean 4 formalisation concerning the p-adic valuations of
Romik's sequence d(n) = 1, 1, -1, 51, 849, -26199, ..., the Taylor coefficients of the Jacobi
theta constant θ₃ at the CM point τ = i, at primes p ≡ 3 (mod 4).

Status: draft. It has not been peer reviewed.

## Contents

| Path | What it is |
|---|---|
| `paper/romik-valuation.tex` | The paper. Build with `latexmk -pdf romik-valuation.tex`. |
| `lean/` | Lean 4 + Mathlib formalisation. See `lean/README.md` for the correspondence with the paper. |
| `romik/` | Python scripts for the numerical checks quoted in the paper, and `d800.pkl`, the values d(0), ..., d(800). |

## Statements

Numbers refer to the paper.

- **Theorem 1.1.** For p ≡ 3 (mod 4), m = ⌊4n/(p+1)⌋ and r = n − m(p+1)/4:
  v_p(d(n)) ≥ v_p((4n)!) − v_p((pm)!), with equality if and only if p ∤ d(r).
- **Corollary 1.2.** v_p(d(n)) ≥ ⌊4n/p²⌋. This is Conjecture 45 of Krattenthaler and Müller
  (arXiv:2304.11471).
- **Theorem 1.5 and Corollary 1.6.** Bounds for Romik's auxiliary sequences u(n), v(n), which give
  parts (1) and (2) of Conjecture 43 of the same paper.
- **Theorem 7.1.** L(ψ^(8n+1), 4n+1) = ϖ^(8n+1) 4^(n−1) d(n)² / (π^(4n) (4n)!) and
  L(ψ^(8n+5), 4n+3) = 0, where ψ is the Hecke character of y² = x³ − x and ϖ is the lemniscate
  constant.

## How each statement is supported

| Statement | Paper proof | Lean | Numerical check |
|---|---|---|---|
| Theorem 1.5, Corollary 1.6 (i), (ii) | Section 6 | complete, from the recurrences | `uv_check.py` |
| Section 2 (ring D, factorisation) | Section 2 | the conclusions used later, for rational coefficients | `lower_bound_check.py` |
| Theorems 1.1, 1.4, Corollary 1.2 | Sections 3–5 | deduced from two cited inputs, which are hypotheses of the Lean theorems | `main_theorem_check.py`, `lean_hypotheses_check.py` |
| Proposition 4.1 (d(n) as Taylor coefficients of σ√℘) | Section 4 | not formalised; a hypothesis of `romik_main` | `lean_hypotheses_check.py`, `recursion_check.py` |
| Theorem 7.1, Corollary 7.2 | Section 7 | not formalised | `hecke_l_check.py`, `l_value_proof_check.py` |

The two cited inputs are the bounds of Bannai, Kobayashi and Yasuda for the coefficients of the
Weierstrass zeta function at supersingular primes (Math. Z. 286 (2017), Corollary 5.5) and
Proposition 4.1 of the paper.

## Reproducing

Lean (the first command downloads the Mathlib build cache, about 7 GB):

    cd lean
    lake exe cache get
    lake build

Numerical checks (Python 3 with `mpmath` and `gmpy2`; run from the directory `romik/`; the
times are approximate):

    python3 romik.py 1600 d800.pkl                   # recompute d(n) for n <= 800
    python3 main_theorem_check.py d800.pkl 1000      # Theorem 1.1 and the data of Section 8 (1 s)
    python3 lean_hypotheses_check.py 1200 d800.pkl   # hypotheses of the Lean theorem romik_main (10 s)
    python3 recursion_check.py d800.pkl 200          # Romik's recursion for d(n) (45 s)
    python3 lower_bound_check.py 1200 1000000 d800.pkl   # the ring D and the leading congruence (25 s)
    python3 uv.py 1200 uv1200.pkl                    # the sequences u(n), v(n) (45 s)
    python3 uv_check.py uv1200.pkl 300               # Theorem 1.5 and Lemma 6.2 (75 s)
    python3 hecke_l_check.py d800.pkl 8 --other-curves   # Theorem 7.1 against the L-series (10 s)
    python3 l_value_proof_check.py d800.pkl 10       # the steps in the proof of Theorem 7.1 (2 s)

Every script stops with an error if a check fails.
