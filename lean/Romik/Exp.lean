import Romik.Factor

/-!
# The factorisation of `exp(L)` (Proposition 2.4)

Over `ℚ`, with the `p`-adic norm. For a power series `g` with zero constant term,
`expSeries g = exp(g)` is Mathlib's `(PowerSeries.exp ℚ).subst g`.

* `coeff_expSeries`, `derivative_expSeries` : the coefficient formula and `exp(g)' = g' exp(g)`;
* `ode_unique` : a solution of `F' = A F` is determined by its constant term;
* `inPD_expSeries_sub_one` : Lemma 2.3(c), `exp(px) ∈ 1 + pD`;
* `isLow_expSeries` : Lemma 2.3(d), `exp(Q) ∈ 𝒪[z]_{≤p} + pJ` for integral `Q` of order `≥ 4`;
* `factorisation` : Proposition 2.4. If `L = Σ ℓ_n z^n` has order `≥ 4`, `ℓ_n` is integral for
  `n ≤ p`, `p ℓ_{p+1}` is integral and `v_p(ℓ_n) ≥ 1 - τ_n` for `n ≥ p + 2`, and if `f' = L' f`
  with `f(0) = 1`, then `f ∈ D` and `p^m m! f_{(p+1)m+s} ≡ (p ℓ_{p+1})^m f_s (mod p)`.
-/

open Nat PowerSeries

namespace Romik

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The exponential of a power series -/

/-- `exp(g)` for a power series `g` (meaningful when `g` has zero constant term). -/
noncomputable def expSeries (g : ℚ⟦X⟧) : ℚ⟦X⟧ := (exp ℚ).subst g

theorem coeff_pow_eq_zero {g : ℚ⟦X⟧} (hg : constantCoeff g = 0) {n k : ℕ} (h : n < k) :
    coeff n (g ^ k) = 0 := by
  obtain ⟨g₁, rfl⟩ := X_dvd_iff.mpr hg
  rw [mul_pow, coeff_X_pow_mul', ite_eq_right (not_le.mpr h)]

theorem coeff_expSeries {g : ℚ⟦X⟧} (hg : constantCoeff g = 0) (n : ℕ) :
    coeff n (expSeries g) = ∑ k ∈ Finset.range (n + 1), (1 / (k ! : ℚ)) * coeff n (g ^ k) := by
  unfold expSeries
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
  rw [finsum_eq_sum_of_support_subset]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_exp]
    simp
  · intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hk (by rw [coeff_pow_eq_zero hg (by omega), smul_zero])

theorem constantCoeff_expSeries {g : ℚ⟦X⟧} (hg : constantCoeff g = 0) :
    constantCoeff (expSeries g) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_expSeries hg]
  simp

theorem derivative_expSeries {g : ℚ⟦X⟧} (hg : constantCoeff g = 0) :
    d⁄dX (expSeries g) = d⁄dX g * expSeries g := by
  unfold expSeries
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hg), derivative_exp, mul_comm]

/-- A solution of `F' = A F` is determined by its constant term. -/
theorem ode_unique {A F G : ℚ⟦X⟧} (hF : d⁄dX F = A * F) (hG : d⁄dX G = A * G)
    (h0 : constantCoeff F = constantCoeff G) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h0]
    · have h1 := congrArg (coeff n) hF
      have h2 := congrArg (coeff n) hG
      rw [coeff_derivative, coeff_mul] at h1 h2
      have hsum : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, coeff ij.1 A * coeff ij.2 F
          = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, coeff ij.1 A * coeff ij.2 G := by
        refine Finset.sum_congr rfl fun ij hij => ?_
        have hsum' : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        rw [ih ij.2 (by omega)]
      have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
      have h3 : coeff (n + 1) F * ((n : ℚ) + 1) = coeff (n + 1) G * ((n : ℚ) + 1) := by
        rw [h1, h2, hsum]
      exact mul_right_cancel₀ hn h3

/-! ### Closure properties -/

theorem IsInt.mul {f g : ℚ⟦X⟧} (hf : IsInt p f) (hg : IsInt p g) : IsInt p (f * g) := fun n => by
  rw [coeff_mul]
  refine padicNorm.sum_le' (fun ij _ => ?_) zero_le_one
  rw [padicNorm.mul]
  calc padicNorm p (coeff ij.1 f) * padicNorm p (coeff ij.2 g) ≤ 1 * 1 :=
        mul_le_mul (hf _) (hg _) (padicNorm.nonneg _) zero_le_one
    _ = 1 := one_mul 1

omit hp in
theorem isInt_one : IsInt p (1 : ℚ⟦X⟧) := fun n => by
  rw [coeff_one]
  split_ifs <;> simp

theorem IsInt.pow {f : ℚ⟦X⟧} (hf : IsInt p f) (k : ℕ) : IsInt p (f ^ k) := by
  induction k with
  | zero => simpa using isInt_one (p := p)
  | succ k ih => rw [pow_succ]; exact ih.mul hf

theorem InD.pow {f : ℚ⟦X⟧} (hf : InD p f) (k : ℕ) : InD p (f ^ k) := by
  induction k with
  | zero => simpa using inD_one (p := p)
  | succ k ih => rw [pow_succ]; exact ih.mul hf

theorem padicNorm_inv_factorial (k : ℕ) :
    padicNorm p (1 / (k ! : ℚ)) = (p : ℚ) ^ vF p k := by
  have h := padicNorm_factorial (p := p) k
  have hk : padicNorm p (k ! : ℚ) ≠ 0 := padicNorm.ne_zero (by exact_mod_cast factorial_ne_zero k)
  rw [padicNorm.div, padicNorm.one]
  field_simp
  linarith

/-- Lemma 2.3(c): if `x ∈ D` has zero constant term, then `exp(px) - 1 ∈ pD`. -/
theorem inPD_expSeries_sub_one {x : ℚ⟦X⟧} (hx0 : constantCoeff x = 0) (hx : InD p x) :
    InPD p (expSeries (C (p : ℚ) * x) - 1) := fun n => by
  have hg0 : constantCoeff (C (p : ℚ) * x) = 0 := by simp [hx0]
  have hp0 : (0 : ℚ) < p := p_pos
  rw [map_sub, coeff_expSeries hg0, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_mul, add_sub_cancel_right]
  rw [← le_div_iff₀ hp0]
  refine padicNorm.sum_le' (fun k _ => ?_) (by positivity)
  rw [le_div_iff₀ hp0, mul_pow, ← map_pow, coeff_C_mul, padicNorm.mul, padicNorm.mul,
    padicNorm_inv_factorial]
  have hpk := padicNorm_p_pow (p := p) (k + 1)
  have hpk' : padicNorm p ((p : ℚ) ^ (k + 1)) = ((p : ℚ) ^ (k + 1))⁻¹ :=
    eq_inv_of_mul_eq_one_left hpk
  have hv : vF p (k + 1) + 1 ≤ k + 1 := multiplicity_factorial_lt_of_ne_zero p (Nat.succ_ne_zero k)
  have hc := (hx.pow (k + 1)) n
  rw [hpk']
  have hpow : (p : ℚ) ^ vF p (k + 1) * p ≤ (p : ℚ) ^ (k + 1) := by
    calc (p : ℚ) ^ vF p (k + 1) * p = (p : ℚ) ^ (vF p (k + 1) + 1) := (pow_succ _ _).symm
      _ ≤ (p : ℚ) ^ (k + 1) := pow_le_pow_right₀ one_le_p hv
  have hpk0 : (0 : ℚ) < (p : ℚ) ^ (k + 1) := pow_pos hp0 _
  calc (p : ℚ) ^ vF p (k + 1) * (((p : ℚ) ^ (k + 1))⁻¹ * padicNorm p (coeff n (x ^ (k + 1)))) * p
      = ((p : ℚ) ^ vF p (k + 1) * p) * ((p : ℚ) ^ (k + 1))⁻¹
          * padicNorm p (coeff n (x ^ (k + 1))) := by ring
    _ ≤ 1 * (p : ℚ) ^ tau p n := by
        refine mul_le_mul ?_ hc (padicNorm.nonneg _) zero_le_one
        rw [← div_eq_mul_inv, div_le_one hpk0]
        exact hpow
    _ = (p : ℚ) ^ tau p n := one_mul _

/-- If `Q` is integral of order `≥ 4`, the coefficient of `z^n` in `exp(Q)` has valuation at
least `-v_p(⌊n/4⌋!)`. -/
theorem norm_coeff_expSeries_le {Q : ℚ⟦X⟧} (hQ4 : ∀ m, m < 4 → coeff m Q = 0) (hQ : IsInt p Q)
    (n : ℕ) : padicNorm p (coeff n (expSeries Q)) ≤ (p : ℚ) ^ vF p (n / 4) := by
  have hQ0 : constantCoeff Q = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hQ4 0 (by norm_num)
  obtain ⟨Q₁, hQ₁⟩ := X_pow_dvd_iff.mpr hQ4
  rw [coeff_expSeries hQ0]
  refine padicNorm.sum_le' (fun k _ => ?_) (by positivity)
  rw [padicNorm.mul, padicNorm_inv_factorial]
  rcases Nat.lt_or_ge n (4 * k) with hlt | hge
  · have hz : coeff n (Q ^ k) = 0 := by
      rw [hQ₁, mul_pow, ← pow_mul, coeff_X_pow_mul', ite_eq_right (not_le.mpr hlt)]
    rw [hz, padicNorm.zero, mul_zero]
    positivity
  · have hk : k ≤ n / 4 := by omega
    calc (p : ℚ) ^ vF p k * padicNorm p (coeff n (Q ^ k)) ≤ (p : ℚ) ^ vF p k * 1 :=
          mul_le_mul_of_nonneg_left ((hQ.pow k) n) (by positivity)
      _ = (p : ℚ) ^ vF p k := mul_one _
      _ ≤ (p : ℚ) ^ vF p (n / 4) := pow_le_pow_right₀ one_le_p (vF_mono hk)

/-- Lemma 2.3(d): `exp(Q) ∈ 𝒪[z]_{≤p} + pJ` for integral `Q` of order `≥ 4`. -/
theorem isLow_expSeries (hp3 : 3 ≤ p) {Q : ℚ⟦X⟧} (hQ4 : ∀ m, m < 4 → coeff m Q = 0)
    (hQ : IsInt p Q) : IsLow p (expSeries Q) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have h := norm_coeff_expSeries_le hQ4 hQ n
    have h0 : vF p (n / 4) = 0 :=
      multiplicity_eq_zero_of_not_dvd
        (fun hd => absurd (hp.out.dvd_factorial.mp hd) (not_le.mpr (by omega)))
    rwa [h0, pow_zero] at h
  · have h := norm_coeff_expSeries_le hQ4 hQ n
    have hτ := vF_div_four_add_one_le_tau (p := p) hp3 hn
    calc padicNorm p (coeff n (expSeries Q)) * p ≤ (p : ℚ) ^ vF p (n / 4) * p :=
          mul_le_mul_of_nonneg_right h p_pos.le
      _ = (p : ℚ) ^ (vF p (n / 4) + 1) := (pow_succ _ _).symm
      _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p hτ

/-! ### The series `exp(ν y)` -/

omit hp in
theorem constantCoeff_expNuY (ν : ℚ) : constantCoeff (expNuY p ν) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  have h := coeff_expNuY_mul (p := p) ν 0
  simpa using h

/-- `exp(ν y)' = (ν y)' exp(ν y)` for `y = z^{p+1}/p`. -/
theorem derivative_expNuY (ν : ℚ) :
    d⁄dX (expNuY p ν) = d⁄dX (C (ν / p) * X ^ (p + 1)) * expNuY p ν := by
  have hp0 : (p : ℚ) ≠ 0 := (p_pos (p := p)).ne'
  ext n
  rw [coeff_derivative, derivative_C_mul_X_pow, Nat.add_sub_cancel, mul_assoc,
    coeff_C_mul, coeff_X_pow_mul']
  by_cases hd : (p + 1) ∣ n + 1
  · obtain ⟨k, hk⟩ := hd
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by
      rcases k with _ | k
      · omega
      · simp⟩
    have hn : n = (p + 1) * j + p := by
      have : (p + 1) * (j + 1) = (p + 1) * j + (p + 1) := by ring
      omega
    have hle : p ≤ n := by omega
    have hsub : n - p = (p + 1) * j := by omega
    rw [hk, coeff_expNuY_mul, ite_eq_left hle, hsub, coeff_expNuY_mul, Nat.factorial_succ]
    have hj : ((j ! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero j
    have hj1 : ((j : ℚ) + 1) ≠ 0 := by positivity
    have hcast : ((n : ℚ) + 1) = ((p : ℚ) + 1) * ((j : ℚ) + 1) := by
      have h := congrArg (fun t : ℕ => (t : ℚ)) hk
      push_cast at h
      linarith
    push_cast
    rw [hcast]
    field_simp
    ring
  · rw [coeff_expNuY_of_not_dvd ν hd, zero_mul]
    split_ifs with hle
    · have hd' : ¬ (p + 1) ∣ n - p := by
        intro h
        apply hd
        have e : n + 1 = (n - p) + (p + 1) := by omega
        rw [e]
        exact Dvd.dvd.add h (dvd_refl _)
      rw [coeff_expNuY_of_not_dvd ν hd', mul_zero]
    · rw [mul_zero]

/-! ### Proposition 2.4 -/

/-- The factorisation (2) of Proposition 2.4: `f = V · exp(ν y) · (1 + r)` with
`V ∈ 𝒪[z]_{≤p} + pJ`, `r ∈ pD` and `ν = p ℓ_{p+1}` integral. -/
theorem exists_factor (hp3 : 3 ≤ p) (ℓ : ℕ → ℚ) (h4 : ∀ n, n < 4 → ℓ n = 0)
    (ha : ∀ n, n ≤ p → padicNorm p (ℓ n) ≤ 1)
    (hb : padicNorm p (ℓ (p + 1)) ≤ p)
    (hc : ∀ n, p + 2 ≤ n → padicNorm p (ℓ n) * p ≤ (p : ℚ) ^ tau p n)
    (f : ℚ⟦X⟧) (hf0 : constantCoeff f = 1) (hf : d⁄dX f = d⁄dX (mk ℓ) * f) :
    ∃ V r : ℚ⟦X⟧, IsLow p V ∧ InPD p r ∧ padicNorm p ((p : ℚ) * ℓ (p + 1)) ≤ 1 ∧
      f = V * expNuY p ((p : ℚ) * ℓ (p + 1)) * (1 + r) := by
  have hp0 : (0 : ℚ) < p := p_pos
  have hpne : (p : ℚ) ≠ 0 := hp0.ne'
  have hnormp : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
  set Q : ℚ⟦X⟧ := mk fun n => if n ≤ p then ℓ n else 0 with hQdef
  set x : ℚ⟦X⟧ := mk fun n => if p + 2 ≤ n then ℓ n / p else 0 with hxdef
  set ν : ℚ := (p : ℚ) * ℓ (p + 1) with hνdef
  -- the three pieces
  have hQ4 : ∀ m, m < 4 → coeff m Q = 0 := by
    intro m hm
    rw [hQdef, coeff_mk]
    split_ifs
    · exact h4 m hm
    · rfl
  have hQint : IsInt p Q := by
    intro n
    rw [hQdef, coeff_mk]
    split_ifs with h
    · exact ha n h
    · simp
  have hQ0 : constantCoeff Q = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hQ4 0 (by norm_num)
  have hx0 : constantCoeff x = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hxdef, coeff_mk, ite_eq_right (by omega)]
  have hxD : InD p x := by
    intro n
    rw [hxdef, coeff_mk]
    split_ifs with h
    · rw [padicNorm.div, hnormp, div_inv_eq_mul]
      exact hc n h
    · simp only [padicNorm.zero]
      positivity
  have hν : padicNorm p ν ≤ 1 := by
    rw [hνdef, padicNorm.mul, hnormp, inv_mul_le_iff₀ hp0, mul_one]
    exact hb
  have hpx0 : constantCoeff (C (p : ℚ) * x) = 0 := by simp [hx0]
  -- `L = Q + ν y + p x`
  have hL : mk ℓ = Q + C (ν / p) * X ^ (p + 1) + C (p : ℚ) * x := by
    ext n
    simp only [map_add, coeff_mk, coeff_C_mul, coeff_X_pow, hQdef, hxdef, hνdef]
    rcases Nat.lt_trichotomy n (p + 1) with h | h | h
    · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      ring
    · rw [ite_eq_right (by omega), ite_eq_left h, ite_eq_right (by omega), h]
      field_simp
      ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      field_simp
      ring
  -- the product satisfies the same differential equation as `f`
  set g : ℚ⟦X⟧ := expSeries Q * expNuY p ν * (1 + (expSeries (C (p : ℚ) * x) - 1)) with hgdef
  have hg' : g = expSeries Q * expNuY p ν * expSeries (C (p : ℚ) * x) := by
    rw [hgdef]
    ring
  have hgode : d⁄dX g = d⁄dX (mk ℓ) * g := by
    rw [hg', hL]
    simp only [Derivation.leibniz, map_add, smul_eq_mul, derivative_expSeries hQ0,
      derivative_expSeries hpx0, derivative_expNuY]
    ring
  have hg0 : constantCoeff g = 1 := by
    rw [hg', map_mul, map_mul, constantCoeff_expSeries hQ0, constantCoeff_expSeries hpx0,
      constantCoeff_expNuY]
    norm_num
  have hfg : f = g := ode_unique hf hgode (by rw [hf0, hg0])
  have hV : IsLow p (expSeries Q) := isLow_expSeries hp3 hQ4 hQint
  have hr : InPD p (expSeries (C (p : ℚ) * x) - 1) := inPD_expSeries_sub_one hx0 hxD
  exact ⟨expSeries Q, expSeries (C (p : ℚ) * x) - 1, hV, hr, hν, hfg⟩

/-- Proposition 2.4 for `f · w`, where `w ∈ 𝒪[z]_{≤p} + pJ`: `f w ∈ D` and
`p^m m! (fw)_{(p+1)m+s} ≡ (p ℓ_{p+1})^m (fw)_s (mod p)`. -/
theorem factorisation_mul (hp3 : 3 ≤ p) (ℓ : ℕ → ℚ) (h4 : ∀ n, n < 4 → ℓ n = 0)
    (ha : ∀ n, n ≤ p → padicNorm p (ℓ n) ≤ 1)
    (hb : padicNorm p (ℓ (p + 1)) ≤ p)
    (hc : ∀ n, p + 2 ≤ n → padicNorm p (ℓ n) * p ≤ (p : ℚ) ^ tau p n)
    (f : ℚ⟦X⟧) (hf0 : constantCoeff f = 1) (hf : d⁄dX f = d⁄dX (mk ℓ) * f)
    {w : ℚ⟦X⟧} (hw : IsLow p w) :
    InD p (f * w) ∧ ∀ m s, s ≤ p →
      padicNorm p ((p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) (f * w)
        - ((p : ℚ) * ℓ (p + 1)) ^ m * coeff s (f * w)) * p ≤ 1 := by
  obtain ⟨V, r, hV, hr, hν, rfl⟩ := exists_factor hp3 ℓ h4 ha hb hc f hf0 hf
  have e : V * expNuY p ((p : ℚ) * ℓ (p + 1)) * (1 + r) * w
      = (V * w) * expNuY p ((p : ℚ) * ℓ (p + 1)) * (1 + r) := by ring
  rw [e]
  exact ⟨inD_of_factor hν (hV.mul hw) hr,
    fun m s hs => factor_congruence hν (hV.mul hw) hr m s hs⟩

/-- **Proposition 2.4.** Let `L = Σ ℓ_n z^n` have order `≥ 4`, with `ℓ_n` integral for `n ≤ p`,
`p ℓ_{p+1}` integral and `v_p(ℓ_n) ≥ 1 - τ_n` for `n ≥ p + 2`. If `f' = L' f` and `f(0) = 1`
(that is, `f = exp(L)`), then `f ∈ D` and `p^m m! f_{(p+1)m+s} ≡ (p ℓ_{p+1})^m f_s (mod p)`
for all `m` and `0 ≤ s ≤ p`. -/
theorem factorisation (hp3 : 3 ≤ p) (ℓ : ℕ → ℚ) (h4 : ∀ n, n < 4 → ℓ n = 0)
    (ha : ∀ n, n ≤ p → padicNorm p (ℓ n) ≤ 1)
    (hb : padicNorm p (ℓ (p + 1)) ≤ p)
    (hc : ∀ n, p + 2 ≤ n → padicNorm p (ℓ n) * p ≤ (p : ℚ) ^ tau p n)
    (f : ℚ⟦X⟧) (hf0 : constantCoeff f = 1) (hf : d⁄dX f = d⁄dX (mk ℓ) * f) :
    InD p f ∧ ∀ m s, s ≤ p →
      padicNorm p ((p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) f
        - ((p : ℚ) * ℓ (p + 1)) ^ m * coeff s f) * p ≤ 1 := by
  have h := factorisation_mul hp3 ℓ h4 ha hb hc f hf0 hf (isInt_one (p := p)).isLow
  rwa [mul_one] at h

end Romik
