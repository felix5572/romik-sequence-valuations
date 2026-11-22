import Romik.Conj43

/-!
# The bound for Romik's sequence `v(n)`, from the recurrence

`v(n)` is defined by the recurrence of Krattenthaler–Müller (arXiv:2304.11471, Section 2):

  `v(0) = 1`,  `v(n) = 2^(n-1) Π₃(n) - (1/2) Σ_{0<m<n} C(2n, 2m) v(m) v(n-m)`.

The values are integers, but integrality is not needed here, so `vSeq` takes values in `ℚ`.
For a prime `p ≡ 3 (mod 4)` (in fact any prime `p ≥ 3`) this file proves

* `norm_vCoeff_le` : `|v(n)/(2^n (2n)!)|_p ≤ p^⌊2n/(p+1)⌋`;
* `norm_vSeq_le` : if `⌊2n/(p+1)⌋ + c ≤ v_p((2n)!)` then `|v(n)|_p ≤ p^(-c)`,

which is the bound for `v(n)` in Theorem 1.5 of `paper/romik-valuation.tex`.
-/

open Nat Finset

namespace Romik

variable {p : ℕ} [hp : Fact p.Prime]

/-- Romik's sequence `v(n)`, by the recurrence of Krattenthaler–Müller. -/
def vSeq : ℕ → ℚ
  | 0 => 1
  | n + 1 => (2 : ℚ) ^ n * (Pi3 (n + 1) : ℚ) - (1 / 2) * ∑ m : Fin n,
      ((2 * (n + 1)).choose (2 * ((m : ℕ) + 1)) : ℚ) * vSeq ((m : ℕ) + 1) * vSeq (n - m)
termination_by n => n
decreasing_by
  all_goals
    have := m.isLt
    omega

/-- The normalised coefficient `v(n)/(2^n (2n)!)`. -/
noncomputable def vCoeff (n : ℕ) : ℚ := vSeq n / ((2 : ℚ) ^ n * ((2 * n)! : ℚ))

theorem vCoeff_zero : vCoeff 0 = 1 := by
  simp [vCoeff, vSeq]

theorem vCoeff_succ (n : ℕ) :
    vCoeff (n + 1) = (1 / 2) * ((Pi3 (n + 1) : ℚ) / ((2 * (n + 1))! : ℚ))
      - (1 / 2) * ∑ m : Fin n, vCoeff ((m : ℕ) + 1) * vCoeff (n - m) := by
  unfold vCoeff
  rw [vSeq]
  have hfac : ((2 * (n + 1))! : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have h2 : ((2 : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [sub_div]
  congr 1
  · rw [pow_succ]
    field_simp
  · rw [mul_div_assoc, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm : (m : ℕ) < n := m.isLt
    have hle : 2 * ((m : ℕ) + 1) ≤ 2 * (n + 1) := by omega
    have hch := Nat.choose_mul_factorial_mul_factorial hle
    have hsub : 2 * (n + 1) - 2 * ((m : ℕ) + 1) = 2 * (n - m) := by omega
    rw [hsub] at hch
    have hq : ((2 * (n + 1)).choose (2 * ((m : ℕ) + 1)) : ℚ) * ((2 * ((m : ℕ) + 1))! : ℚ)
        * ((2 * (n - m))! : ℚ) = ((2 * (n + 1))! : ℚ) := by exact_mod_cast hch
    have hpow : (2 : ℚ) ^ (n + 1) = (2 : ℚ) ^ ((m : ℕ) + 1) * (2 : ℚ) ^ (n - m) := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : ((2 * ((m : ℕ) + 1))! : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
    have h4 : ((2 * (n - m))! : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
    have h5 : ((2 * (n + 1)).choose (2 * ((m : ℕ) + 1)) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hle).ne'
    have h6 : ((2 : ℚ) ^ ((m : ℕ) + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h7 : ((2 : ℚ) ^ (n - m)) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hpow, ← hq]
    field_simp

/-- `|1/2|_p = 1` for an odd prime `p`. -/
theorem padicNorm_half (hp2 : p ≠ 2) : padicNorm p (1 / 2 : ℚ) = 1 := by
  have h : padicNorm p ((2 : ℕ) : ℚ) = 1 := by
    rw [padicNorm.nat_eq_one_iff]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hdvd)
  rw [padicNorm.div, padicNorm.one]
  have h' : padicNorm p (2 : ℚ) = 1 := by exact_mod_cast h
  rw [h', div_one]

/-- `|2^n|_p = 1` for an odd prime `p`. -/
theorem padicNorm_two_pow (hp2 : p ≠ 2) (n : ℕ) : padicNorm p ((2 : ℚ) ^ n) = 1 := by
  have h : padicNorm p ((2 ^ n : ℕ) : ℚ) = 1 := by
    rw [padicNorm.nat_eq_one_iff]
    intro hdvd
    have h2 : p ∣ 2 := hp.out.dvd_of_dvd_pow hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)
  exact_mod_cast h

/-- Theorem 1.5 for `v`: `|v(n)/(2^n (2n)!)|_p ≤ p^⌊2n/(p+1)⌋`. -/
theorem norm_vCoeff_le (hp3 : 3 ≤ p) (n : ℕ) :
    padicNorm p (vCoeff n) ≤ (p : ℚ) ^ (2 * n / (p + 1)) := by
  have hp2 : p ≠ 2 := by omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [vCoeff_zero, padicNorm.one]
      exact one_le_pow₀ one_le_p
    · rw [vCoeff_succ]
      refine le_trans padicNorm.sub (max_le ?_ ?_)
      · rw [padicNorm.mul, padicNorm_half hp2, one_mul]
        apply padicNorm_div_le (Pi3_ne_zero _) (factorial_ne_zero _)
        rw [multiplicity_Pi3]
        exact vF_two_mul_le hp3 (n + 1)
      · rw [padicNorm.mul, padicNorm_half hp2, one_mul]
        refine padicNorm.sum_le' (fun m _ => ?_) (by positivity)
        have hm : (m : ℕ) < n := m.isLt
        rw [padicNorm.mul]
        have hA := ih ((m : ℕ) + 1) (by omega)
        have hB := ih (n - m) (by omega)
        have hexp : 2 * ((m : ℕ) + 1) / (p + 1) + 2 * (n - m) / (p + 1)
            ≤ 2 * (n + 1) / (p + 1) := by
          have h := Nat.div_add_div_le_add_div (x := 2 * ((m : ℕ) + 1)) (y := 2 * (n - m))
            (z := p + 1)
          have e : 2 * ((m : ℕ) + 1) + 2 * (n - m) = 2 * (n + 1) := by omega
          rw [e] at h
          exact h
        calc padicNorm p (vCoeff ((m : ℕ) + 1)) * padicNorm p (vCoeff (n - m))
            ≤ (p : ℚ) ^ (2 * ((m : ℕ) + 1) / (p + 1)) * (p : ℚ) ^ (2 * (n - m) / (p + 1)) :=
              mul_le_mul hA hB (padicNorm.nonneg _) (by positivity)
          _ = (p : ℚ) ^ (2 * ((m : ℕ) + 1) / (p + 1) + 2 * (n - m) / (p + 1)) :=
              (pow_add _ _ _).symm
          _ ≤ (p : ℚ) ^ (2 * (n + 1) / (p + 1)) := pow_le_pow_right₀ one_le_p hexp

/-- If `⌊2n/(p+1)⌋ + c ≤ v_p((2n)!)` then `|v(n)|_p ≤ p^(-c)`, i.e. `v_p(v(n)) ≥ c`. -/
theorem norm_vSeq_le (hp3 : 3 ≤ p) {n c : ℕ} (h : 2 * n / (p + 1) + c ≤ vF p (2 * n)) :
    padicNorm p (vSeq n) * (p : ℚ) ^ c ≤ 1 := by
  have hp2 : p ≠ 2 := by omega
  have hfac : ((2 * n)! : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have h2 : ((2 : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hv : vSeq n = vCoeff n * ((2 : ℚ) ^ n * ((2 * n)! : ℚ)) := by
    unfold vCoeff
    field_simp
  have hpow2 := padicNorm_two_pow (p := p) hp2 n
  have hF := padicNorm_factorial (p := p) (2 * n)
  have hp0 : (0 : ℚ) < p := p_pos
  rw [hv, padicNorm.mul, padicNorm.mul, hpow2, one_mul]
  calc padicNorm p (vCoeff n) * padicNorm p ((2 * n)! : ℚ) * (p : ℚ) ^ c
      ≤ (p : ℚ) ^ (2 * n / (p + 1)) * padicNorm p ((2 * n)! : ℚ) * (p : ℚ) ^ c :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_vCoeff_le hp3 n) (padicNorm.nonneg _)) (by positivity)
    _ = padicNorm p ((2 * n)! : ℚ) * (p : ℚ) ^ (2 * n / (p + 1) + c) := by
        rw [pow_add]
        ring
    _ ≤ padicNorm p ((2 * n)! : ℚ) * (p : ℚ) ^ vF p (2 * n) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_p h) (padicNorm.nonneg _)
    _ = 1 := hF

end Romik
