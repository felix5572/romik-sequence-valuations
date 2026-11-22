import Romik.Tau

/-!
# The ring `D` and the last step of the factorisation

This file formalises, over `ℚ` with the `p`-adic norm, the ring-theoretic part of the proof of
Proposition 2.4 of `paper/romik-valuation.tex`:

* `InD`, `InPD`, `IsInt`, `IsLow` : the conditions `f ∈ D`, `f ∈ pD`, `f ∈ ℤ_(p)[[z]]`,
  `f ∈ 𝒪[z]_{≤p} + pJ`;
* `InD.mul`, `InD.mul_inPD`, `inPD_X_pow_mul` : Lemma 2.3(a),(b);
* `leading_congruence`, `inD_of_factor`, `factor_congruence` : if `f = V · exp(ν y) · (1 + r)`
  with `V ∈ 𝒪[z]_{≤p} + pJ`, `ν` integral and `r ∈ pD`, then `f ∈ D` and
  `p^m m! f_{(p+1)m+s} ≡ ν^m f_s (mod p)` for `0 ≤ s ≤ p`.

The exponential series and the factorisation itself are in `Romik/Exp.lean`.
-/

open Nat PowerSeries

namespace Romik

variable {p : ℕ} [hp : Fact p.Prime]

theorem one_le_p : (1 : ℚ) ≤ p := by exact_mod_cast hp.out.one_le

theorem p_pos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos

theorem tau_mono {a b : ℕ} (h : a ≤ b) : tau p a ≤ tau p b :=
  vF_mono (Nat.mul_le_mul_left p (Nat.div_le_div_right h))

theorem tau_mul_add {m s : ℕ} (hs : s ≤ p) : tau p ((p + 1) * m + s) = m + vF p m := by
  have h : ((p + 1) * m + s) / (p + 1) = m := by
    rw [Nat.mul_add_div (Nat.succ_pos p), Nat.div_eq_of_lt (by omega), add_zero]
  rw [tau_eq, h]

/-! ### `p`-adic norms of `p^m` and `m!` -/

theorem padicNorm_p_pow (m : ℕ) : padicNorm p ((p : ℚ) ^ m) * (p : ℚ) ^ m = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, padicNorm.mul, padicNorm.padicNorm_p_of_prime]
    have h : (p : ℚ) ≠ 0 := (p_pos (p := p)).ne'
    calc padicNorm p ((p : ℚ) ^ m) * (p : ℚ)⁻¹ * ((p : ℚ) ^ m * p)
        = padicNorm p ((p : ℚ) ^ m) * (p : ℚ) ^ m * ((p : ℚ)⁻¹ * p) := by ring
      _ = 1 := by rw [ih, inv_mul_cancel₀ h, mul_one]

theorem padicNorm_factorial (k : ℕ) : padicNorm p (k ! : ℚ) * (p : ℚ) ^ vF p k = 1 := by
  have hk : ((k ! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero k
  rw [padicNorm.eq_zpow_of_ne_zero hk, padicValRat.of_nat, zpow_neg, zpow_natCast]
  exact inv_mul_cancel₀ (pow_ne_zero _ (p_pos (p := p)).ne')

theorem padicNorm_pow_le_one {ν : ℚ} (hν : padicNorm p ν ≤ 1) (k : ℕ) :
    padicNorm p (ν ^ k) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, padicNorm.mul]
    calc padicNorm p (ν ^ k) * padicNorm p ν ≤ 1 * 1 :=
          mul_le_mul ih hν (padicNorm.nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-! ### The conditions `f ∈ D`, `f ∈ pD`, `f` integral -/

/-- `f ∈ D`: the coefficient of `z^n` has `p`-adic valuation at least `-τ_n`. -/
def InD (p : ℕ) (f : ℚ⟦X⟧) : Prop := ∀ n, padicNorm p (coeff n f) ≤ (p : ℚ) ^ tau p n

/-- `f ∈ pD`: the coefficient of `z^n` has `p`-adic valuation at least `1 - τ_n`. -/
def InPD (p : ℕ) (f : ℚ⟦X⟧) : Prop := ∀ n, padicNorm p (coeff n f) * p ≤ (p : ℚ) ^ tau p n

/-- `f ∈ ℤ_(p)[[z]]`. -/
def IsInt (p : ℕ) (f : ℚ⟦X⟧) : Prop := ∀ n, padicNorm p (coeff n f) ≤ 1

theorem InPD.inD {f : ℚ⟦X⟧} (h : InPD p f) : InD p f := fun n =>
  le_trans (le_mul_of_one_le_right (padicNorm.nonneg _) one_le_p) (h n)

theorem IsInt.inD {f : ℚ⟦X⟧} (h : IsInt p f) : InD p f := fun n =>
  le_trans (h n) (one_le_pow₀ one_le_p)

theorem inD_one : InD p (1 : ℚ⟦X⟧) := IsInt.inD fun n => by
  rw [coeff_one]
  split_ifs <;> simp

theorem InD.add {f g : ℚ⟦X⟧} (hf : InD p f) (hg : InD p g) : InD p (f + g) := fun n => by
  rw [map_add]
  exact le_trans padicNorm.nonarchimedean (max_le (hf n) (hg n))

/-- Lemma 2.3(a): `D` is closed under multiplication. -/
theorem InD.mul {f g : ℚ⟦X⟧} (hf : InD p f) (hg : InD p g) : InD p (f * g) := fun n => by
  rw [coeff_mul]
  refine padicNorm.sum_le' (fun ij hij => ?_) (by positivity)
  have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [padicNorm.mul]
  calc padicNorm p (coeff ij.1 f) * padicNorm p (coeff ij.2 g)
      ≤ (p : ℚ) ^ tau p ij.1 * (p : ℚ) ^ tau p ij.2 :=
        mul_le_mul (hf _) (hg _) (padicNorm.nonneg _) (by positivity)
    _ = (p : ℚ) ^ (tau p ij.1 + tau p ij.2) := (pow_add _ _ _).symm
    _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p (hsum ▸ tau_add _ _)

/-- Lemma 2.3(a): `pD` is an ideal of `D`. -/
theorem InD.mul_inPD {f g : ℚ⟦X⟧} (hf : InD p f) (hg : InPD p g) : InPD p (f * g) := fun n => by
  rw [coeff_mul, ← le_div_iff₀ p_pos]
  refine padicNorm.sum_le' (fun ij hij => ?_) (by positivity)
  have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [padicNorm.mul, le_div_iff₀ p_pos]
  calc padicNorm p (coeff ij.1 f) * padicNorm p (coeff ij.2 g) * p
      = padicNorm p (coeff ij.1 f) * (padicNorm p (coeff ij.2 g) * p) := by ring
    _ ≤ (p : ℚ) ^ tau p ij.1 * (p : ℚ) ^ tau p ij.2 :=
        mul_le_mul (hf _) (hg _) (mul_nonneg (padicNorm.nonneg _) p_pos.le) (by positivity)
    _ = (p : ℚ) ^ (tau p ij.1 + tau p ij.2) := (pow_add _ _ _).symm
    _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p (hsum ▸ tau_add _ _)

/-- Lemma 2.3(b): `z^{p+1} D ⊂ pD`. -/
theorem inPD_X_pow_mul {g : ℚ⟦X⟧} (hg : InD p g) : InPD p (X ^ (p + 1) * g) := fun n => by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · have hτ : tau p (n - (p + 1)) + 1 ≤ tau p n := by
      have := tau_add_succ (p := p) (n - (p + 1))
      rwa [Nat.sub_add_cancel h] at this
    calc padicNorm p (coeff (n - (p + 1)) g) * p
        ≤ (p : ℚ) ^ tau p (n - (p + 1)) * p := mul_le_mul_of_nonneg_right (hg _) p_pos.le
      _ = (p : ℚ) ^ (tau p (n - (p + 1)) + 1) := (pow_succ _ _).symm
      _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p hτ
  · simp

/-! ### The leading term -/

/-- `exp(ν y) = Σ_k ν^k y^k / k!` with `y = z^{p+1}/p`. -/
noncomputable def expNuY (p : ℕ) (ν : ℚ) : ℚ⟦X⟧ :=
  mk fun n => if (p + 1) ∣ n then
    ν ^ (n / (p + 1)) / ((p : ℚ) ^ (n / (p + 1)) * ((n / (p + 1)) ! : ℚ)) else 0

omit hp in
theorem coeff_expNuY_mul (ν : ℚ) (k : ℕ) :
    coeff ((p + 1) * k) (expNuY p ν) = ν ^ k / ((p : ℚ) ^ k * (k ! : ℚ)) := by
  rw [expNuY, coeff_mk]
  split_ifs with h
  · rw [Nat.mul_div_cancel_left k (Nat.succ_pos p)]
  · exact absurd (Dvd.intro k rfl) h

omit hp in
theorem coeff_expNuY_of_not_dvd (ν : ℚ) {n : ℕ} (h : ¬ (p + 1) ∣ n) :
    coeff n (expNuY p ν) = 0 := by
  simp [expNuY, coeff_mk, h]

theorem padicNorm_expNuY_term {ν : ℚ} (hν : padicNorm p ν ≤ 1) (k : ℕ) :
    padicNorm p (ν ^ k / ((p : ℚ) ^ k * (k ! : ℚ))) ≤ (p : ℚ) ^ (k + vF p k) := by
  have h1 : padicNorm p ((p : ℚ) ^ k) = ((p : ℚ) ^ k)⁻¹ :=
    eq_inv_of_mul_eq_one_left (padicNorm_p_pow k)
  have h2 : padicNorm p (k ! : ℚ) = ((p : ℚ) ^ vF p k)⁻¹ :=
    eq_inv_of_mul_eq_one_left (padicNorm_factorial k)
  rw [padicNorm.div, padicNorm.mul, h1, h2, pow_add, ← mul_inv, div_inv_eq_mul]
  exact mul_le_of_le_one_left (by positivity) (padicNorm_pow_le_one hν k)

theorem inD_expNuY {ν : ℚ} (hν : padicNorm p ν ≤ 1) : InD p (expNuY p ν) := fun n => by
  by_cases h : (p + 1) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [coeff_expNuY_mul]
    have e : tau p ((p + 1) * k) = k + vF p k := by
      simpa using tau_mul_add (p := p) (m := k) (s := 0) (Nat.zero_le p)
    rw [e]
    exact padicNorm_expNuY_term hν k
  · rw [coeff_expNuY_of_not_dvd ν h]
    simp only [padicNorm.zero]
    positivity

/-- `V ∈ 𝒪[z]_{≤ p} + pJ`: integral coefficients up to degree `p`, and coefficients of
valuation at least `1 - τ_n` from degree `p + 1` on. -/
def IsLow (p : ℕ) (V : ℚ⟦X⟧) : Prop :=
  (∀ n, n ≤ p → padicNorm p (coeff n V) ≤ 1) ∧
    ∀ n, p + 1 ≤ n → padicNorm p (coeff n V) * p ≤ (p : ℚ) ^ tau p n

theorem IsLow.inD {V : ℚ⟦X⟧} (hV : IsLow p V) : InD p V := fun n => by
  rcases Nat.lt_or_ge p n with h | h
  · exact le_trans (le_mul_of_one_le_right (padicNorm.nonneg _) one_le_p) (hV.2 n h)
  · exact le_trans (hV.1 n h) (one_le_pow₀ one_le_p)

theorem IsInt.isLow {V : ℚ⟦X⟧} (hV : IsInt p V) : IsLow p V :=
  ⟨fun n _ => hV n, fun n hn => by
    have h1 : 1 ≤ tau p n := le_trans (Nat.div_pos hn (Nat.succ_pos p)) (le_tau n)
    calc padicNorm p (coeff n V) * p ≤ 1 * p := mul_le_mul_of_nonneg_right (hV n) p_pos.le
      _ = (p : ℚ) ^ 1 := by rw [one_mul, pow_one]
      _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p h1⟩

/-- Lemma 2.3(e): `𝒪[z]_{≤p} + pJ` is closed under multiplication. -/
theorem IsLow.mul {V W : ℚ⟦X⟧} (hV : IsLow p V) (hW : IsLow p W) : IsLow p (V * W) := by
  have hp0 : (0 : ℚ) < p := p_pos
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [coeff_mul]
    refine padicNorm.sum_le' (fun ij hij => ?_) zero_le_one
    have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [padicNorm.mul]
    calc padicNorm p (coeff ij.1 V) * padicNorm p (coeff ij.2 W) ≤ 1 * 1 :=
          mul_le_mul (hV.1 _ (by omega)) (hW.1 _ (by omega)) (padicNorm.nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have h1 : 1 ≤ tau p n := le_trans (Nat.div_pos hn (Nat.succ_pos p)) (le_tau n)
    rw [coeff_mul, ← le_div_iff₀ hp0]
    refine padicNorm.sum_le' (fun ij hij => ?_) (by positivity)
    have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [padicNorm.mul, le_div_iff₀ hp0]
    have ha0 : (0 : ℚ) ≤ padicNorm p (coeff ij.1 V) := padicNorm.nonneg _
    have hb0 : (0 : ℚ) ≤ padicNorm p (coeff ij.2 W) := padicNorm.nonneg _
    have hadd : tau p ij.1 + tau p ij.2 ≤ tau p n := hsum ▸ tau_add _ _
    rcases Nat.lt_or_ge p ij.1 with hi | hi <;> rcases Nat.lt_or_ge p ij.2 with hj | hj
    · calc padicNorm p (coeff ij.1 V) * padicNorm p (coeff ij.2 W) * p
          ≤ (padicNorm p (coeff ij.1 V) * p) * (padicNorm p (coeff ij.2 W) * p) := by
            nlinarith [mul_nonneg ha0 hb0, one_le_p (p := p),
              mul_nonneg (mul_nonneg ha0 hb0) hp0.le]
        _ ≤ (p : ℚ) ^ tau p ij.1 * (p : ℚ) ^ tau p ij.2 :=
            mul_le_mul (hV.2 _ hi) (hW.2 _ hj) (mul_nonneg hb0 hp0.le) (by positivity)
        _ = (p : ℚ) ^ (tau p ij.1 + tau p ij.2) := (pow_add _ _ _).symm
        _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p hadd
    · calc padicNorm p (coeff ij.1 V) * padicNorm p (coeff ij.2 W) * p
          = (padicNorm p (coeff ij.1 V) * p) * padicNorm p (coeff ij.2 W) := by ring
        _ ≤ (p : ℚ) ^ tau p ij.1 * 1 :=
            mul_le_mul (hV.2 _ hi) (hW.1 _ hj) hb0 (by positivity)
        _ = (p : ℚ) ^ tau p ij.1 := mul_one _
        _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p (tau_mono (by omega))
    · calc padicNorm p (coeff ij.1 V) * padicNorm p (coeff ij.2 W) * p
          = padicNorm p (coeff ij.1 V) * (padicNorm p (coeff ij.2 W) * p) := by ring
        _ ≤ 1 * (p : ℚ) ^ tau p ij.2 :=
            mul_le_mul (hV.1 _ hi) (hW.2 _ hj) (mul_nonneg hb0 hp0.le) zero_le_one
        _ = (p : ℚ) ^ tau p ij.2 := one_mul _
        _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p (tau_mono (by omega))
    · calc padicNorm p (coeff ij.1 V) * padicNorm p (coeff ij.2 W) * p
          ≤ 1 * 1 * p :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (hV.1 _ hi) (hW.1 _ hj) hb0 zero_le_one) hp0.le
        _ = (p : ℚ) ^ 1 := by rw [one_mul, one_mul, pow_one]
        _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p h1

/-- The coefficient of `z^{(p+1)m+s}` in `V · exp(ν y)` is `V_s ν^m/(p^m m!)` modulo `pD`. -/
theorem coeff_mul_expNuY {ν : ℚ} (hν : padicNorm p ν ≤ 1) {V : ℚ⟦X⟧} (hV : IsLow p V)
    (m s : ℕ) (hs : s ≤ p) :
    padicNorm p (coeff ((p + 1) * m + s) (V * expNuY p ν)
      - coeff s V * (ν ^ m / ((p : ℚ) ^ m * (m ! : ℚ)))) * p
      ≤ (p : ℚ) ^ tau p ((p + 1) * m + s) := by
  have hmem : (s, (p + 1) * m) ∈ Finset.HasAntidiagonal.antidiagonal ((p + 1) * m + s) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    omega
  rw [coeff_mul, ← coeff_expNuY_mul ν m, ← Finset.sum_erase_eq_sub hmem, ← le_div_iff₀ p_pos]
  refine padicNorm.sum_le' (fun ij hij => ?_) (by positivity)
  rw [le_div_iff₀ p_pos]
  obtain ⟨hne, hij'⟩ := Finset.mem_erase.mp hij
  have hsum : ij.1 + ij.2 = (p + 1) * m + s := Finset.HasAntidiagonal.mem_antidiagonal.mp hij'
  by_cases hd : (p + 1) ∣ ij.2
  · obtain ⟨k, hk⟩ := hd
    have hkm : k < m := by
      by_contra hge
      have hge' : m ≤ k := not_lt.mp hge
      rcases Nat.lt_or_eq_of_le hge' with hlt | heq
      · have h1 : (p + 1) * (m + 1) ≤ (p + 1) * k := Nat.mul_le_mul_left _ hlt
        rw [Nat.mul_succ] at h1
        omega
      · apply hne
        have h2 : ij.2 = (p + 1) * m := by rw [hk, heq]
        have h1 : ij.1 = s := by omega
        exact Prod.ext h1 h2
    have hi : p + 1 ≤ ij.1 := by
      have h1 : (p + 1) * (k + 1) ≤ (p + 1) * m := Nat.mul_le_mul_left _ hkm
      rw [Nat.mul_succ] at h1
      omega
    have hτ : tau p ij.1 + (k + vF p k) ≤ tau p ((p + 1) * m + s) := by
      have h3 : tau p ((p + 1) * k) = k + vF p k := by
        simpa using tau_mul_add (p := p) (m := k) (s := 0) (Nat.zero_le p)
      have h4 := tau_add (p := p) ij.1 ((p + 1) * k)
      rw [← hk, hsum] at h4
      rw [hk] at h4
      omega
    rw [padicNorm.mul, hk, coeff_expNuY_mul]
    calc padicNorm p (coeff ij.1 V) * padicNorm p (ν ^ k / ((p : ℚ) ^ k * (k ! : ℚ))) * p
        = (padicNorm p (coeff ij.1 V) * p) * padicNorm p (ν ^ k / ((p : ℚ) ^ k * (k ! : ℚ))) := by
          ring
      _ ≤ (p : ℚ) ^ tau p ij.1 * (p : ℚ) ^ (k + vF p k) :=
          mul_le_mul (hV.2 _ hi) (padicNorm_expNuY_term hν k) (padicNorm.nonneg _) (by positivity)
      _ = (p : ℚ) ^ (tau p ij.1 + (k + vF p k)) := (pow_add _ _ _).symm
      _ ≤ (p : ℚ) ^ tau p ((p + 1) * m + s) := pow_le_pow_right₀ one_le_p hτ
  · rw [coeff_expNuY_of_not_dvd ν hd]
    simp only [mul_zero, padicNorm.zero, zero_mul]
    positivity

/-- If `f = V · exp(ν y) · (1 + r)` with `V ∈ 𝒪[z]_{≤p} + pJ`, `ν` integral and `r ∈ pD`,
then `p^m m! f_{(p+1)m+s} ≡ ν^m V_s (mod p)`. -/
theorem leading_congruence {ν : ℚ} (hν : padicNorm p ν ≤ 1) {V r : ℚ⟦X⟧} (hV : IsLow p V)
    (hr : InPD p r) (m s : ℕ) (hs : s ≤ p) :
    padicNorm p ((p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) (V * expNuY p ν * (1 + r))
      - ν ^ m * coeff s V) * p ≤ 1 := by
  set n := (p + 1) * m + s with hn
  set g := V * expNuY p ν with hg
  have hgD : InD p g := hV.inD.mul (inD_expNuY hν)
  have h1 := coeff_mul_expNuY hν hV m s hs
  have h2 := (hgD.mul_inPD hr) n
  have hpm : (p : ℚ) ^ m ≠ 0 := pow_ne_zero _ (p_pos (p := p)).ne'
  have hfm : ((m ! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero m
  have hx : padicNorm p (coeff n (g * (1 + r))
      - coeff s V * (ν ^ m / ((p : ℚ) ^ m * (m ! : ℚ)))) * p ≤ (p : ℚ) ^ tau p n := by
    have e : coeff n (g * (1 + r)) - coeff s V * (ν ^ m / ((p : ℚ) ^ m * (m ! : ℚ)))
        = (coeff n g - coeff s V * (ν ^ m / ((p : ℚ) ^ m * (m ! : ℚ)))) + coeff n (g * r) := by
      rw [mul_add, mul_one, map_add]
      ring
    rw [e]
    have hmax := padicNorm.nonarchimedean (p := p)
      (q := coeff n g - coeff s V * (ν ^ m / ((p : ℚ) ^ m * (m ! : ℚ)))) (r := coeff n (g * r))
    rcases le_max_iff.mp hmax with h | h
    · exact le_trans (mul_le_mul_of_nonneg_right h p_pos.le) h1
    · exact le_trans (mul_le_mul_of_nonneg_right h p_pos.le) h2
  have e : (p : ℚ) ^ m * (m ! : ℚ) * coeff n (g * (1 + r)) - ν ^ m * coeff s V
      = (p : ℚ) ^ m * (m ! : ℚ) * (coeff n (g * (1 + r))
        - coeff s V * (ν ^ m / ((p : ℚ) ^ m * (m ! : ℚ)))) := by
    field_simp
  have hτ : tau p n = m + vF p m := tau_mul_add hs
  rw [e, padicNorm.mul, padicNorm.mul]
  have hA := padicNorm_p_pow (p := p) m
  have hB := padicNorm_factorial (p := p) m
  rw [hτ, pow_add] at hx
  have hA0 : (0 : ℚ) ≤ padicNorm p ((p : ℚ) ^ m) := padicNorm.nonneg _
  have hB0 : (0 : ℚ) ≤ padicNorm p (m ! : ℚ) := padicNorm.nonneg _
  calc padicNorm p ((p : ℚ) ^ m) * padicNorm p (m ! : ℚ)
        * padicNorm p (coeff n (g * (1 + r)) - coeff s V * (ν ^ m / ((p : ℚ) ^ m * (m ! : ℚ)))) * p
      = padicNorm p ((p : ℚ) ^ m) * padicNorm p (m ! : ℚ)
        * (padicNorm p (coeff n (g * (1 + r))
          - coeff s V * (ν ^ m / ((p : ℚ) ^ m * (m ! : ℚ)))) * p) := by ring
    _ ≤ padicNorm p ((p : ℚ) ^ m) * padicNorm p (m ! : ℚ)
        * ((p : ℚ) ^ m * (p : ℚ) ^ vF p m) :=
        mul_le_mul_of_nonneg_left hx (mul_nonneg hA0 hB0)
    _ = (padicNorm p ((p : ℚ) ^ m) * (p : ℚ) ^ m)
        * (padicNorm p (m ! : ℚ) * (p : ℚ) ^ vF p m) := by ring
    _ = 1 := by rw [hA, hB, mul_one]

/-- Under the same hypotheses, `f ∈ D`. -/
theorem inD_of_factor {ν : ℚ} (hν : padicNorm p ν ≤ 1) {V r : ℚ⟦X⟧} (hV : IsLow p V)
    (hr : InPD p r) : InD p (V * expNuY p ν * (1 + r)) :=
  (hV.inD.mul (inD_expNuY hν)).mul (inD_one.add hr.inD)

/-- The congruence (3) of Proposition 2.4: `p^m m! f_{(p+1)m+s} ≡ ν^m f_s (mod p)`. -/
theorem factor_congruence {ν : ℚ} (hν : padicNorm p ν ≤ 1) {V r : ℚ⟦X⟧} (hV : IsLow p V)
    (hr : InPD p r) (m s : ℕ) (hs : s ≤ p) :
    padicNorm p ((p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) (V * expNuY p ν * (1 + r))
      - ν ^ m * coeff s (V * expNuY p ν * (1 + r))) * p ≤ 1 := by
  have h1 := leading_congruence hν hV hr m s hs
  have h0 := leading_congruence hν hV hr 0 s hs
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul, mul_zero,
    zero_add] at h0
  set f := V * expNuY p ν * (1 + r) with hf
  have e : (p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) f - ν ^ m * coeff s f
      = ((p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) f - ν ^ m * coeff s V)
        - ν ^ m * (coeff s f - coeff s V) := by ring
  rw [e]
  have hmax := padicNorm.sub (p := p)
    (q := (p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) f - ν ^ m * coeff s V)
    (r := ν ^ m * (coeff s f - coeff s V))
  rcases le_max_iff.mp hmax with h | h
  · exact le_trans (mul_le_mul_of_nonneg_right h p_pos.le) h1
  · refine le_trans (mul_le_mul_of_nonneg_right h p_pos.le) ?_
    rw [padicNorm.mul]
    calc padicNorm p (ν ^ m) * padicNorm p (coeff s f - coeff s V) * p
        = padicNorm p (ν ^ m) * (padicNorm p (coeff s f - coeff s V) * p) := by ring
      _ ≤ 1 * 1 := mul_le_mul (padicNorm_pow_le_one hν m) h0
          (mul_nonneg (padicNorm.nonneg _) p_pos.le) zero_le_one
      _ = 1 := one_mul 1

end Romik
