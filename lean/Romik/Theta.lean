import Romik.Sigma
import Romik.VSeq

/-!
# The factor `√℘`, and Theorem 1.1 assuming the cited inputs

Let `p ≡ 3 (mod 4)`, let `ζ(z) = 1/z + Σ b_n z^n` be the Weierstrass zeta function of
`y² = 4x³ - g₂ x`, and put `f = σ(z)/z`, `w = √(z² ℘(z))`. As formal power series these are
characterised by

* `f(0) = 1`, `f' = (Σ b_n z^n) f`;
* `w(0) = 1`, `w² = z² ℘(z) = 1 - z² (Σ b_n z^n)'`   (because `℘ = -ζ'`).

`theta_congruence` proves that `σ√℘ = f w` lies in `D` and satisfies the leading congruence,
assuming only the bounds of [BKY, Corollary 5.5] for the `b_n`. The proof does not use
logarithms: `z² ℘ ∈ R`, so `w ∈ R ⊂ 𝒪[z]_{≤p} + pJ`, and that class is closed under
multiplication, so `w` can be absorbed into the factor `V` of Proposition 2.4.

`romik_main` is Theorem 1.1(i), the equality criterion of Theorem 1.1(ii) and Corollary 1.2
for any sequence `d` with `d(k) = (4k)!/2^k · [z^{4k}] (f w)`. Its hypotheses are exactly the
cited inputs:

* `hsmall`, `hall`, `hcop` : [BKY, Corollary 5.5];
* `hunit` : `v_p(b_p) = -1`, [BKY, Proposition 4.3];
* `hd` : the identification of Romik's sequence, Proposition 4.1 of the paper (with `g₂ = 4`).
-/

open Nat PowerSeries

namespace Romik

variable {p : ℕ} [hp : Fact p.Prime]

/-- The ring `R` of Section 3: `v_p(r_n) ≥ -⌊n/(p² - 1)⌋`. -/
def InR (p : ℕ) (g : ℚ⟦X⟧) : Prop := ∀ n, padicNorm p (coeff n g) ≤ (p : ℚ) ^ (n / (p ^ 2 - 1))

/-- `R ⊂ 𝒪[z]_{≤p} + pJ`. -/
theorem InR.isLow (hp3 : 3 ≤ p) {g : ℚ⟦X⟧} (hg : InR p g) : IsLow p g := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have h := hg n
    have hlt : n < p ^ 2 - 1 := by
      have h3 : p * 3 ≤ p * p := Nat.mul_le_mul_left p hp3
      rw [pow_two]
      omega
    rwa [Nat.div_eq_of_lt hlt, pow_zero] at h
  · have h2 := two_mul_div_le hp3 n
    have h1 : 1 ≤ n / (p + 1) := Nat.div_pos hn (Nat.succ_pos p)
    have h3 := le_tau (p := p) n
    calc padicNorm p (coeff n g) * p ≤ (p : ℚ) ^ (n / (p ^ 2 - 1)) * p :=
          mul_le_mul_of_nonneg_right (hg n) p_pos.le
      _ = (p : ℚ) ^ (n / (p ^ 2 - 1) + 1) := (pow_succ _ _).symm
      _ ≤ (p : ℚ) ^ tau p n := pow_le_pow_right₀ one_le_p (by omega)

/-- If `g ∈ R` and `w² = g`, `w(0) = 1`, then `w ∈ R` (`p` odd). -/
theorem inR_sqrt (hp2 : p ≠ 2) {w g : ℚ⟦X⟧} (hw0 : constantCoeff w = 1) (hsq : w ^ 2 = g)
    (hg : InR p g) : InR p w := by
  have h0 : coeff 0 w = 1 := by rw [coeff_zero_eq_constantCoeff_apply, hw0]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [h0, padicNorm.one]
      exact one_le_pow₀ one_le_p
    · have hrec : coeff (n + 1) w = (1 / 2) * (coeff (n + 1) g
          - ∑ k ∈ Finset.range n, coeff (k + 1) w * coeff (n - k) w) := by
        have h := congrArg (coeff (n + 1)) hsq
        rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.sum_range_succ, Finset.sum_range_succ'] at h
        simp only [Nat.sub_zero, Nat.sub_self, h0, Nat.add_sub_add_right] at h
        linarith
      rw [hrec, padicNorm.mul, padicNorm_half hp2, one_mul]
      refine le_trans padicNorm.sub (max_le (hg _) ?_)
      refine padicNorm.sum_le' (fun k hk => ?_) (by positivity)
      have hk' : k < n := Finset.mem_range.mp hk
      rw [padicNorm.mul]
      have hA := ih (k + 1) (by omega)
      have hB := ih (n - k) (by omega)
      have hexp : (k + 1) / (p ^ 2 - 1) + (n - k) / (p ^ 2 - 1) ≤ (n + 1) / (p ^ 2 - 1) := by
        have h := Nat.div_add_div_le_add_div (x := k + 1) (y := n - k) (z := p ^ 2 - 1)
        have e : k + 1 + (n - k) = n + 1 := by omega
        rw [e] at h
        exact h
      calc padicNorm p (coeff (k + 1) w) * padicNorm p (coeff (n - k) w)
          ≤ (p : ℚ) ^ ((k + 1) / (p ^ 2 - 1)) * (p : ℚ) ^ ((n - k) / (p ^ 2 - 1)) :=
            mul_le_mul hA hB (padicNorm.nonneg _) (by positivity)
        _ = (p : ℚ) ^ ((k + 1) / (p ^ 2 - 1) + (n - k) / (p ^ 2 - 1)) := (pow_add _ _ _).symm
        _ ≤ (p : ℚ) ^ ((n + 1) / (p ^ 2 - 1)) := pow_le_pow_right₀ one_le_p hexp

/-- `z² ℘(z) = 1 - z² (Σ b_n z^n)'` lies in `R`; this is [BKY, Corollary 5.3], here deduced
from the bounds of [BKY, Corollary 5.5]. -/
theorem inR_wp (b : ℕ → ℚ)
    (hall : ∀ n, p ≤ n → padicNorm p (b n) ≤ (p : ℚ) ^ (1 + (n - p) / (p ^ 2 - 1)))
    (hcop : ∀ n, ¬ p ∣ n → padicNorm p (b n) ≤ (p : ℚ) ^ ((n + 1) / (p ^ 2 - 1))) :
    InR p (1 - X ^ 2 * d⁄dX (mk b)) := by
  have hp0 : (0 : ℚ) < p := p_pos
  intro n
  rw [map_sub, coeff_one, coeff_X_pow_mul']
  by_cases h2 : 2 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hne : k + 2 ≠ 0 := by omega
    simp only [hne, h2, ↓reduceIte, Nat.add_sub_cancel]
    rw [zero_sub, padicNorm.neg, coeff_derivative, coeff_mk, padicNorm.mul]
    have hcast : ((k : ℚ) + 1) = ((k + 1 : ℕ) : ℚ) := by
      push_cast
      rfl
    rw [hcast]
    by_cases hd : p ∣ k + 1
    · obtain ⟨c, hc⟩ := hd
      have hk1 : padicNorm p ((k + 1 : ℕ) : ℚ) ≤ (p : ℚ)⁻¹ := by
        rw [hc, Nat.cast_mul, padicNorm.mul, padicNorm.padicNorm_p_of_prime]
        exact mul_le_of_le_one_right (inv_nonneg.mpr hp0.le) (padicNorm.of_nat c)
      have hb := hall (k + 1) (Nat.le_of_dvd (Nat.succ_pos k) ⟨c, hc⟩)
      calc padicNorm p (b (k + 1)) * padicNorm p ((k + 1 : ℕ) : ℚ)
          ≤ (p : ℚ) ^ (1 + (k + 1 - p) / (p ^ 2 - 1)) * (p : ℚ)⁻¹ :=
            mul_le_mul hb hk1 (padicNorm.nonneg _) (by positivity)
        _ = (p : ℚ) ^ ((k + 1 - p) / (p ^ 2 - 1)) := by
            rw [add_comm, pow_succ, mul_assoc, mul_inv_cancel₀ hp0.ne', mul_one]
        _ ≤ (p : ℚ) ^ ((k + 2) / (p ^ 2 - 1)) :=
            pow_le_pow_right₀ one_le_p (Nat.div_le_div_right (by omega))
    · have hb : padicNorm p (b (k + 1)) ≤ (p : ℚ) ^ ((k + 2) / (p ^ 2 - 1)) := hcop (k + 1) hd
      calc padicNorm p (b (k + 1)) * padicNorm p ((k + 1 : ℕ) : ℚ)
          ≤ (p : ℚ) ^ ((k + 2) / (p ^ 2 - 1)) * 1 :=
            mul_le_mul hb (padicNorm.of_nat _) (padicNorm.nonneg _) (by positivity)
        _ = (p : ℚ) ^ ((k + 2) / (p ^ 2 - 1)) := mul_one _
  · simp only [h2, ↓reduceIte, sub_zero]
    split_ifs
    · rw [padicNorm.one]
      exact one_le_pow₀ one_le_p
    · rw [padicNorm.zero]
      positivity

/-- **Theorem 1.1 in terms of `σ√℘`**, assuming the bounds of [BKY, Corollary 5.5]: the series
`f w = σ(z) √℘(z)` lies in `D` and satisfies the leading congruence with `ν = p b_p/(p+1)`. -/
theorem theta_congruence (hp4 : p % 4 = 3) (b : ℕ → ℚ)
    (hsupp : ∀ n, n % 4 ≠ 3 → b n = 0)
    (hsmall : ∀ n, n < p → padicNorm p (b n) ≤ 1)
    (hall : ∀ n, p ≤ n → padicNorm p (b n) ≤ (p : ℚ) ^ (1 + (n - p) / (p ^ 2 - 1)))
    (hcop : ∀ n, ¬ p ∣ n → padicNorm p (b n) ≤ (p : ℚ) ^ ((n + 1) / (p ^ 2 - 1)))
    (f : ℚ⟦X⟧) (hf0 : constantCoeff f = 1) (hf : d⁄dX f = mk b * f)
    (w : ℚ⟦X⟧) (hw0 : constantCoeff w = 1) (hw : w ^ 2 = 1 - X ^ 2 * d⁄dX (mk b)) :
    InD p (f * w) ∧ ∀ m s, s ≤ p →
      padicNorm p ((p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) (f * w)
        - ((p : ℚ) * (b p / ((p : ℚ) + 1))) ^ m * coeff s (f * w)) * p ≤ 1 :=
  sigma_mul_congruence hp4 b hsupp hsmall hall hcop f hf0 hf
    ((inR_sqrt (by omega) hw0 hw (inR_wp b hall hcop)).isLow (by omega))

/-- If `|x - y|_p < 1`, then `x` is a `p`-adic unit if and only if `y` is. -/
theorem norm_eq_one_iff_of_close {x y : ℚ} (h : padicNorm p (x - y) * p ≤ 1) :
    padicNorm p x = 1 ↔ padicNorm p y = 1 := by
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hlt : padicNorm p (x - y) < 1 := by
    by_contra hge
    have h1 : 1 ≤ padicNorm p (x - y) := not_lt.mp hge
    have h2 : (p : ℚ) ≤ padicNorm p (x - y) * p := by
      calc (p : ℚ) = 1 * p := (one_mul _).symm
        _ ≤ padicNorm p (x - y) * p := mul_le_mul_of_nonneg_right h1 p_pos.le
    linarith
  constructor
  · intro hx
    by_contra hy
    have hne : padicNorm p x ≠ padicNorm p (-y) := by
      rw [padicNorm.neg, hx]
      exact fun h => hy h.symm
    have hmax := padicNorm.add_eq_max_of_ne hne
    rw [← sub_eq_add_neg, hx] at hmax
    have h1 : 1 ≤ padicNorm p (x - y) := by
      rw [hmax]
      exact le_max_left _ _
    linarith
  · intro hy
    by_contra hx
    have hne : padicNorm p x ≠ padicNorm p (-y) := by
      rw [padicNorm.neg, hy]
      exact hx
    have hmax := padicNorm.add_eq_max_of_ne hne
    rw [← sub_eq_add_neg, padicNorm.neg, hy] at hmax
    have h1 : 1 ≤ padicNorm p (x - y) := by
      rw [hmax]
      exact le_max_right _ _
    linarith

theorem padicNorm_pow_eq_one {ν : ℚ} (hν : padicNorm p ν = 1) (k : ℕ) :
    padicNorm p (ν ^ k) = 1 := by
  induction k with
  | zero => rw [pow_zero, padicNorm.one]
  | succ k ih => rw [pow_succ, padicNorm.mul, ih, hν, one_mul]

/-- From `h ∈ D` and the leading congruence with a unit `ν` to the valuation of
`d(k) = (4k)!/2^k · h_{4k}`: the lower bound, the equality criterion, and `v_p(d(n)) ≥ ⌊4n/p²⌋`. -/
theorem valuation_of_congruence (hp4 : p % 4 = 3) {h : ℚ⟦X⟧} {ν : ℚ} (hD : InD p h)
    (hcong : ∀ m s, s ≤ p → padicNorm p ((p : ℚ) ^ m * (m ! : ℚ) * coeff ((p + 1) * m + s) h
      - ν ^ m * coeff s h) * p ≤ 1)
    (hν : padicNorm p ν = 1)
    (d : ℕ → ℚ) (hd : ∀ k, d k = ((4 * k)! : ℚ) / 2 ^ k * coeff (4 * k) h) (n : ℕ) :
    padicNorm p (d n) * (p : ℚ) ^ vF p (4 * n) ≤ (p : ℚ) ^ tau p (4 * n) ∧
    (∀ m r, 4 * n = (p + 1) * m + 4 * r → 4 * r ≤ p →
      (padicNorm p (d n) * (p : ℚ) ^ vF p (4 * n) = (p : ℚ) ^ tau p (4 * n)
        ↔ padicNorm p (d r) = 1)) ∧
    padicNorm p (d n) * (p : ℚ) ^ (4 * n / p ^ 2) ≤ 1 := by
  have hp2 : p ≠ 2 := by omega
  have hp0 : (0 : ℚ) < p := p_pos
  have hnd : ∀ k, padicNorm p (d k) * (p : ℚ) ^ vF p (4 * k) = padicNorm p (coeff (4 * k) h) := by
    intro k
    rw [hd, padicNorm.mul, padicNorm.div, padicNorm_two_pow hp2, div_one]
    have hF := padicNorm_factorial (p := p) (4 * k)
    linear_combination padicNorm p (coeff (4 * k) h) * hF
  have hpos : (0 : ℚ) < (p : ℚ) ^ tau p (4 * n) := pow_pos hp0 _
  have hlow : padicNorm p (d n) * (p : ℚ) ^ vF p (4 * n) ≤ (p : ℚ) ^ tau p (4 * n) := by
    rw [hnd]
    exact hD (4 * n)
  refine ⟨hlow, fun m r hmr hr => ?_, ?_⟩
  · have hv0 : vF p (4 * r) = 0 := by
      unfold vF
      exact multiplicity_eq_zero_of_not_dvd fun hdvd => by
        have := (hp.out.dvd_factorial).mp hdvd
        omega
    have hdr : padicNorm p (d r) = padicNorm p (coeff (4 * r) h) := by
      have hr0 := hnd r
      rwa [hv0, pow_zero, mul_one] at hr0
    have hY : padicNorm p (ν ^ m * coeff (4 * r) h) = padicNorm p (d r) := by
      rw [padicNorm.mul, padicNorm_pow_eq_one hν, one_mul, hdr]
    have htau : tau p (4 * n) = m + vF p m := by
      rw [hmr]
      exact tau_mul_add hr
    have hX : padicNorm p ((p : ℚ) ^ m * (m ! : ℚ) * coeff (4 * n) h) * (p : ℚ) ^ tau p (4 * n)
        = padicNorm p (coeff (4 * n) h) := by
      rw [htau, padicNorm.mul, padicNorm.mul, pow_add]
      have h1 := padicNorm_p_pow (p := p) m
      have h2 := padicNorm_factorial (p := p) m
      linear_combination
        (padicNorm p (m ! : ℚ) * (p : ℚ) ^ vF p m * padicNorm p (coeff (4 * n) h)) * h1
          + padicNorm p (coeff (4 * n) h) * h2
    have hc := hcong m (4 * r) hr
    rw [← hmr] at hc
    have hiff := norm_eq_one_iff_of_close hc
    rw [hY] at hiff
    rw [hnd, ← hiff]
    constructor
    · intro hEq
      exact mul_right_cancel₀ hpos.ne' ((hX.trans hEq).trans (one_mul _).symm)
    · intro hEq
      rw [← hX, hEq, one_mul]
  · have h2 := tau_add_div_sq_le (p := p) (4 * n)
    have h3 : padicNorm p (d n) * (p : ℚ) ^ (4 * n / p ^ 2) * (p : ℚ) ^ tau p (4 * n)
        ≤ 1 * (p : ℚ) ^ tau p (4 * n) := by
      calc padicNorm p (d n) * (p : ℚ) ^ (4 * n / p ^ 2) * (p : ℚ) ^ tau p (4 * n)
          = padicNorm p (d n) * (p : ℚ) ^ (tau p (4 * n) + 4 * n / p ^ 2) := by
            rw [pow_add]
            ring
        _ ≤ padicNorm p (d n) * (p : ℚ) ^ vF p (4 * n) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_p h2) (padicNorm.nonneg _)
        _ ≤ (p : ℚ) ^ tau p (4 * n) := hlow
        _ = 1 * (p : ℚ) ^ tau p (4 * n) := (one_mul _).symm
    exact le_of_mul_le_mul_right h3 hpos

/-- **Theorem 1.1 and Corollary 1.2**, assuming the cited inputs (see the file header).
For `p ≡ 3 (mod 4)` and `4n = (p+1)m + 4r`, `0 ≤ 4r ≤ p`:

1. `v_p(d(n)) ≥ v_p((4n)!) - τ_{4n}`;
2. equality holds if and only if `d(r)` is a `p`-adic unit;
3. `v_p(d(n)) ≥ ⌊4n/p²⌋`. -/
theorem romik_main (hp4 : p % 4 = 3) (b : ℕ → ℚ)
    (hsupp : ∀ n, n % 4 ≠ 3 → b n = 0)
    (hsmall : ∀ n, n < p → padicNorm p (b n) ≤ 1)
    (hall : ∀ n, p ≤ n → padicNorm p (b n) ≤ (p : ℚ) ^ (1 + (n - p) / (p ^ 2 - 1)))
    (hcop : ∀ n, ¬ p ∣ n → padicNorm p (b n) ≤ (p : ℚ) ^ ((n + 1) / (p ^ 2 - 1)))
    (hunit : padicNorm p (b p) = p)
    (f : ℚ⟦X⟧) (hf0 : constantCoeff f = 1) (hf : d⁄dX f = mk b * f)
    (w : ℚ⟦X⟧) (hw0 : constantCoeff w = 1) (hw : w ^ 2 = 1 - X ^ 2 * d⁄dX (mk b))
    (d : ℕ → ℚ) (hd : ∀ k, d k = ((4 * k)! : ℚ) / 2 ^ k * coeff (4 * k) (f * w)) (n : ℕ) :
    padicNorm p (d n) * (p : ℚ) ^ vF p (4 * n) ≤ (p : ℚ) ^ tau p (4 * n) ∧
    (∀ m r, 4 * n = (p + 1) * m + 4 * r → 4 * r ≤ p →
      (padicNorm p (d n) * (p : ℚ) ^ vF p (4 * n) = (p : ℚ) ^ tau p (4 * n)
        ↔ padicNorm p (d r) = 1)) ∧
    padicNorm p (d n) * (p : ℚ) ^ (4 * n / p ^ 2) ≤ 1 := by
  have hp0 : (0 : ℚ) < p := p_pos
  have hθ := theta_congruence hp4 b hsupp hsmall hall hcop f hf0 hf w hw0 hw
  have hν : padicNorm p ((p : ℚ) * (b p / ((p : ℚ) + 1))) = 1 := by
    have h1 : padicNorm p ((p : ℚ) + 1) = 1 := by
      have h := (padicNorm.nat_eq_one_iff (p := p) (p + 1)).mpr fun hdvd => by
        have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp hdvd
        have := Nat.le_of_dvd Nat.one_pos h1
        have := hp.out.two_le
        omega
      push_cast at h
      exact h
    rw [padicNorm.mul, padicNorm.div, padicNorm.padicNorm_p_of_prime, hunit, h1, div_one]
    exact inv_mul_cancel₀ hp0.ne'
  exact valuation_of_congruence hp4 hθ.1 hθ.2 hν d hd n

end Romik
