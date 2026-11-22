import Romik.Exp

/-!
# Theorem 1.4, assuming the bounds of Bannai–Kobayashi–Yasuda

Let `p ≡ 3 (mod 4)` and let `ζ(z) = 1/z + Σ_{n ≥ 1} b_n z^n` be the Weierstrass zeta function of
`y² = 4x³ - g₂ x`, so that `b_n = 0` unless `n ≡ 3 (mod 4)`, and `f(z) = σ(z)/z` satisfies
`f' = (Σ b_n z^n) f`, `f(0) = 1`.

The bounds of [BKY, Corollary 5.5] for the `b_n`, in the integer form used in the proof of
Proposition 3.4 of the paper, are taken as hypotheses:

* `hsmall` : `b_n` is `p`-integral for `n < p`;
* `hall`   : `v_p(b_n) ≥ -1 - ⌊(n - p)/(p² - 1)⌋` for `n ≥ p`;
* `hcop`   : `v_p(b_n) ≥ -⌊(n + 1)/(p² - 1)⌋` if `p ∤ n`.

`sigma_congruence` then gives `f ∈ D` and
`p^m m! f_{(p+1)m+s} ≡ ν^m f_s (mod p)` with `ν = p b_p/(p+1)`, which is Theorem 1.4
(`f_n = a_{n+1}`). Nothing here is specific to elliptic curves: the statement is about any
sequence `b` satisfying the three bounds.
-/

open Nat PowerSeries

namespace Romik

variable {p : ℕ} [hp : Fact p.Prime]

/-- `|1/n|_p = p^{v_p(n)}` for `n ≠ 0`. -/
theorem padicNorm_inv_nat {n : ℕ} (hn : n ≠ 0) :
    padicNorm p (1 / (n : ℚ)) = (p : ℚ) ^ multiplicity p n := by
  have hp0 : (p : ℚ) ≠ 0 := (p_pos (p := p)).ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [padicNorm.div, padicNorm.one, padicNorm.eq_zpow_of_ne_zero hn', padicValRat.of_nat,
    zpow_neg, zpow_natCast, one_div, inv_inv]

/-- The coefficients of `log(σ(z)/z)`: `ℓ_n = b_{n-1}/n`. -/
noncomputable def logCoeff (b : ℕ → ℚ) (n : ℕ) : ℚ := if n = 0 then 0 else b (n - 1) / n

theorem derivative_mk_logCoeff (b : ℕ → ℚ) : d⁄dX (mk (logCoeff b)) = mk b := by
  ext n
  rw [coeff_derivative, coeff_mk, coeff_mk, logCoeff, ite_eq_right (Nat.succ_ne_zero n),
    Nat.add_sub_cancel]
  have h : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- Theorem 1.4 for `f · w` with `w ∈ 𝒪[z]_{≤p} + pJ`, assuming the bounds of
[BKY, Corollary 5.5] for the coefficients `b_n` of the Weierstrass zeta function. -/
theorem sigma_mul_congruence (hp4 : p % 4 = 3) (b : ℕ → ℚ)
    (hsupp : ∀ n, n % 4 ≠ 3 → b n = 0)
    (hsmall : ∀ n, n < p → padicNorm p (b n) ≤ 1)
    (hall : ∀ n, p ≤ n → padicNorm p (b n) ≤ (p : ℚ) ^ (1 + (n - p) / (p ^ 2 - 1)))
    (hcop : ∀ n, ¬ p ∣ n → padicNorm p (b n) ≤ (p : ℚ) ^ ((n + 1) / (p ^ 2 - 1)))
    (f : ℚ⟦X⟧) (hf0 : constantCoeff f = 1) (hf : d⁄dX f = mk b * f)
    {w : ℚ⟦X⟧} (hw : IsLow p w) :
    InD p (f * w) ∧ ∀ m s, s ≤ p →
      padicNorm p ((p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) (f * w)
        - ((p : ℚ) * (b p / ((p : ℚ) + 1))) ^ m * coeff s (f * w)) * p ≤ 1 := by
  have hp3 : 3 ≤ p := by omega
  have hp0 : (0 : ℚ) < p := p_pos
  -- `ℓ_n` vanishes unless `4 ∣ n`, `n ≥ 4`
  have hzero : ∀ n, ¬ 4 ∣ n → logCoeff b n = 0 := by
    intro n hn
    unfold logCoeff
    split_ifs with h0
    · rfl
    · rw [hsupp (n - 1) (by omega), zero_div]
  have hnorm : ∀ n, n ≠ 0 →
      padicNorm p (logCoeff b n) = padicNorm p (b (n - 1)) * (p : ℚ) ^ multiplicity p n := by
    intro n hn
    unfold logCoeff
    rw [ite_eq_right hn, div_eq_mul_one_div, padicNorm.mul, padicNorm_inv_nat hn]
  have hℓ := factorisation_mul hp3 (logCoeff b)
    (fun n hn => by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simp [logCoeff]
      · exact hzero n (fun ⟨c, hc⟩ => by omega))
    (fun n hn => by
      by_cases h4 : 4 ∣ n
      · rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          simp [logCoeff]
        · have hnp : n < p := by
            rcases h4 with ⟨c, hc⟩
            omega
          have hndvd : ¬ p ∣ n := Nat.not_dvd_of_pos_of_lt hpos hnp
          rw [hnorm n (by omega), multiplicity_eq_zero_of_not_dvd hndvd, pow_zero, mul_one]
          exact hsmall (n - 1) (by omega)
      · rw [hzero n h4]
        simp)
    (by
      have hndvd : ¬ p ∣ p + 1 := by
        intro h
        have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h
        have := Nat.le_of_dvd Nat.one_pos h1
        omega
      rw [hnorm (p + 1) (Nat.succ_ne_zero p), multiplicity_eq_zero_of_not_dvd hndvd, pow_zero,
        mul_one, Nat.add_sub_cancel]
      have h := hall p (le_refl p)
      simpa using h)
    (fun n hn => by
      by_cases h4 : 4 ∣ n
      · rw [hnorm n (by omega)]
        by_cases hd : p ∣ n - 1
        · -- `p ∣ n - 1`, hence `p ∤ n`
          have hndvd : ¬ p ∣ n := by
            intro h
            have h1 : p ∣ n - (n - 1) := Nat.dvd_sub h hd
            have e : n - (n - 1) = 1 := by omega
            rw [e] at h1
            have := Nat.le_of_dvd Nat.one_pos h1
            omega
          have hv := verify_dvd_pred (p := p) hp3 hp4 hn h4 hd
          have hb1 := hall (n - 1) (Nat.le_of_dvd (by omega) hd)
          rw [multiplicity_eq_zero_of_not_dvd hndvd, pow_zero, mul_one]
          have e : n - 1 - p = n - 1 - p := rfl
          calc padicNorm p (b (n - 1)) * p
              ≤ (p : ℚ) ^ (1 + (n - 1 - p) / (p ^ 2 - 1)) * p :=
                mul_le_mul_of_nonneg_right hb1 hp0.le
            _ = (p : ℚ) ^ ((n - 1 - p) / (p ^ 2 - 1) + 2) := by
                rw [← pow_succ]
                congr 1
                omega
            _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p hv
        · have hv := verify_valuation (p := p) hp3 hn h4
          have hb1 := hcop (n - 1) hd
          have e : n - 1 + 1 = n := by omega
          rw [e] at hb1
          calc padicNorm p (b (n - 1)) * (p : ℚ) ^ multiplicity p n * p
              ≤ (p : ℚ) ^ (n / (p ^ 2 - 1)) * (p : ℚ) ^ multiplicity p n * p :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hb1 (by positivity)) hp0.le
            _ = (p : ℚ) ^ (n / (p ^ 2 - 1) + multiplicity p n + 1) := by ring
            _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p hv
      · rw [hzero n h4]
        simp only [padicNorm.zero, zero_mul]
        positivity)
    f hf0 (by rw [derivative_mk_logCoeff]; exact hf) hw
  have hν : logCoeff b (p + 1) = b p / ((p : ℚ) + 1) := by
    unfold logCoeff
    rw [ite_eq_right (Nat.succ_ne_zero p), Nat.add_sub_cancel]
    push_cast
    rfl
  rw [hν] at hℓ
  exact hℓ

/-- **Theorem 1.4**, assuming the bounds of [BKY, Corollary 5.5] for the coefficients `b_n` of
the Weierstrass zeta function. -/
theorem sigma_congruence (hp4 : p % 4 = 3) (b : ℕ → ℚ)
    (hsupp : ∀ n, n % 4 ≠ 3 → b n = 0)
    (hsmall : ∀ n, n < p → padicNorm p (b n) ≤ 1)
    (hall : ∀ n, p ≤ n → padicNorm p (b n) ≤ (p : ℚ) ^ (1 + (n - p) / (p ^ 2 - 1)))
    (hcop : ∀ n, ¬ p ∣ n → padicNorm p (b n) ≤ (p : ℚ) ^ ((n + 1) / (p ^ 2 - 1)))
    (f : ℚ⟦X⟧) (hf0 : constantCoeff f = 1) (hf : d⁄dX f = mk b * f) :
    InD p f ∧ ∀ m s, s ≤ p →
      padicNorm p ((p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) f
        - ((p : ℚ) * (b p / ((p : ℚ) + 1))) ^ m * coeff s f) * p ≤ 1 := by
  have h := sigma_mul_congruence hp4 b hsupp hsmall hall hcop f hf0 hf (isInt_one (p := p)).isLow
  rwa [mul_one] at h

end Romik
