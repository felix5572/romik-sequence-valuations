# Lean formalisation

This directory formalises parts of `paper/romik-valuation.tex` in Lean 4.36.0 with Mathlib
v4.36.0. In Lean all coefficients are rational numbers (the case K = ℚ_p); the paper allows a
finite unramified extension of ℚ_p.

    lake exe cache get    # first time: downloads the Mathlib build cache (about 7 GB)
    lake build

There is no `sorry`, and the theorems listed below depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## 1. The sequences u(n), v(n): complete, from the recurrences

| File | Declaration | Content |
|---|---|---|
| `Conj43.lean` | `u`, `Pi1`, `Pi3` | u(n), defined by the integer recurrence of Krattenthaler–Müller, Section 2 (`#eval` gives 1, 6, 256, 28560, ...) |
| | `pow_dvd_u` | the bound for u in Theorem 1.5 |
| | `conj43_one` | Conjecture 43(1): p^(2e−1) ∣ u(n) for e ≥ 1 and 2n+1 ≥ e p² |
| | `conj43_two` | Conjecture 43(2): p^(2e) ∣ u(n) for e = f+2 and 2n+1 ≥ e p² + (e−2)p + 1 |
| `VSeq.lean` | `vSeq` | v(n), defined by its recurrence, as a sequence of rational numbers (`#eval` gives 1, 1, 47, 7395, ...) |
| | `norm_vSeq_le` | the bound for v in Theorem 1.5 |
| `Threshold.lean` | `bound_odd_power` and others | Lemma 6.2 |

## 2. Section 2 of the paper

| File | Declaration | Paper |
|---|---|---|
| `Tau.lean` | `tau_add`, `tau_add_succ` | Lemma 2.2(a) |
| | `vF_div_four_add_one_le_tau` | Lemma 2.2(b) |
| | `two_mul_div_le`, `div_add_le_tau` | Lemma 2.5 |
| | `verify_valuation`, `verify_dvd_pred` | the integer inequalities in the proof of Proposition 3.4 |
| | `tau_add_div_sq_le` | Lemma 5.1 |
| `Factor.lean` | `InD.mul`, `InD.mul_inPD`, `inPD_X_pow_mul` | Lemma 2.3(a), (b) |
| | `IsLow`, `IsLow.mul` | the class Λ and Lemma 2.3(e) |
| | `factor_congruence` | from the factorisation to the leading congruence |
| `Exp.lean` | `inPD_expSeries_sub_one` | Lemma 2.3(c), in the form: if x ∈ D and x(0) = 0, then exp(px) − 1 ∈ pD. The paper's conclusion ∈ pJ also says that the coefficients of low degree vanish; that part is not in the Lean statement. |
| | `isLow_expSeries` | Lemma 2.3(d) |
| | `factorisation`, `factorisation_mul` | Proposition 2.4: if f′ = L′f, f(0) = 1 and the coefficients of L satisfy (a), (b), (c), then f ∈ D and the leading congruence holds; the same after multiplying by w ∈ Λ |
| | `exists_factor` | the factorisation of Proposition 2.4, in the form f = V·exp(νy)·(1+r) with V ∈ Λ and r ∈ pD. The finer statements V(0) = 1 and r ∈ pJ of the paper are not in the Lean statement. |

## 3. Theorems 1.4 and 1.1 and Corollary 1.2, assuming the cited inputs

Let b_n be rational numbers, zero unless n ≡ 3 (mod 4), and let f, w be power series with

    f(0) = 1,  f′ = (Σ b_n zⁿ) f,      w(0) = 1,  w² = 1 − z² (Σ b_n zⁿ)′

For the coefficients of ζ(z) = 1/z + Σ b_n zⁿ these are f = σ(z)/z and w = √(z²℘(z)), because
℘ = −ζ′.

| File | Declaration | Hypotheses | Conclusion |
|---|---|---|---|
| `Sigma.lean` | `sigma_congruence` | the three bounds of BKY17, Corollary 5.5 (`hsmall`, `hall`, `hcop`) | Theorem 1.4: f ∈ D and p^m·m!·f_{(p+1)m+s} ≡ ν^m·f_s (mod p) with ν = p·b_p/(p+1). It does not assert that ν is a unit; that uses `hunit`, which occurs only in `romik_main`. |
| `Theta.lean` | `inR_wp`, `inR_sqrt`, `InR.isLow` | the same | z²℘ ∈ R and √(z²℘) ∈ R ⊂ Λ. What is needed of BKY17, Corollary 5.3 is deduced from Corollary 5.5 and is not a separate hypothesis. |
| | `theta_congruence` | the same | σ√℘ = f·w ∈ D, with the same leading congruence |
| | `romik_main` | the same, and v_p(b_p) = −1 (`hunit`), and d(k) = (4k)!/2^k·[z^{4k}](f·w) (`hd`, Proposition 4.1 of the paper) | Theorem 1.1(i); the criterion for equality in (ii): if 4n = (p+1)m + 4r and 4r ≤ p, then equality holds if and only if d(r) is a p-adic unit; Corollary 1.2: v_p(d(n)) ≥ ⌊4n/p²⌋ |

Every hypothesis of `romik_main` has been checked on the actual coefficients, to degree 1200,
for all primes p ≡ 3 (mod 4) below 1200, and for d(k) with k ≤ 299:

    python3 romik/lean_hypotheses_check.py 1200 romik/d800.pkl

## Not formalised

- Corollary 5.5 of Bannai–Kobayashi–Yasuda (Math. Z. 286 (2017)). It enters as hypotheses;
  `hunit`, that is v_p(b_p) = −1, is the case n = p of the equality statement in that corollary
  (see also their Proposition 4.3).
- The identification of d(n) with Taylor coefficients of σ√℘ (Proposition 4.1 of the paper). It
  enters as the hypothesis `hd`.
- Section 7 of the paper (central values of Hecke L-functions).

So for Theorem 1.1 the deduction from the two cited inputs to the conclusion is formalised, and
the two inputs are not.
