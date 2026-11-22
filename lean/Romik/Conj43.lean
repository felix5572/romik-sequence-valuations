import Romik.Factor
import Romik.Threshold

/-!
# Parts (1) and (2) of Conjecture 43 of Krattenthaler–Müller, from the recurrence

Romik's auxiliary sequence `u(n)` is defined here by the integer recurrence of
Krattenthaler–Müller (arXiv:2304.11471, Section 2):

  `u(n) = Π₁(n) - Σ_{m<n} C(2n+1, 2m+1) Π₃(n-m) u(m)`,
  `Π₁(N) = ∏_{j=1}^{N} (4j-1)²`, `Π₃(N) = ∏_{j=1}^{N} (4j-3)²`.

For a prime `p ≡ 3 (mod 4)` this file proves, with no input from outside Mathlib,

* `norm_u_le` / `pow_dvd_u` : `v_p(u(n)) ≥ v_p((2n+1)!) - ⌊(2n+1)/(p+1)⌋` (Theorem 1.5 for `u`);
* `conj43_one` : `p^(2e-1) ∣ u(n)` whenever `2n+1 ≥ e p²`  (Conjecture 43(1));
* `conj43_two` : `p^(2e) ∣ u(n)` whenever `2n+1 ≥ e p² + (e-2) p + 1`, `e ≥ 2` (Conjecture 43(2)).

The proof follows Section 6 of `paper/romik-valuation.tex`, with the counting in Lemma 6.1
replaced by `v_p(∏_{l<j}(4l+a)) ≥ v_p(j!)` and `v_p(n!) ≤ 2 v_p(⌊n/2⌋!) + ⌊log_p n⌋`.
-/

open Nat Finset

namespace Romik

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Valuations of the products -/

/-- `v_p(n!) ≤ 2 v_p(⌊n/2⌋!) + ⌊log_p n⌋`. -/
theorem vF_le_two_mul_half (n : ℕ) : vF p n ≤ 2 * vF p (n / 2) + Nat.log p n := by
  have hb : Nat.log p n < Nat.log p n + 1 := Nat.lt_succ_self _
  have hb2 : Nat.log p (n / 2) < Nat.log p n + 1 :=
    lt_of_le_of_lt (Nat.log_mono_right (Nat.div_le_self n 2)) hb
  unfold vF
  rw [multiplicity_factorial hb, multiplicity_factorial hb2, Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ i ≤ 2 * (n / 2 / p ^ i) + 1 := by
    intro i _
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm 2 (p ^ i), ← Nat.div_div_eq_div_mul]
    omega
  calc ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ i
      ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), (2 * (n / 2 / p ^ i) + 1) :=
        Finset.sum_le_sum hterm
    _ = ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), 2 * (n / 2 / p ^ i) + Nat.log p n := by
        rw [Finset.sum_add_distrib]
        simp

/-- For `p` odd and `a > 0`: `v_p(∏_{l<j} (4l + a)) ≥ v_p(j!)`. -/
theorem vF_le_multiplicity_prod (hp2 : p ≠ 2) {a : ℕ} (ha : 0 < a) (j : ℕ) :
    vF p j ≤ multiplicity p (∏ l ∈ range j, (4 * l + a)) := by
  have hpN : 1 < p ^ (vF p j + 1) := Nat.one_lt_pow (Nat.succ_ne_zero _) hp.out.one_lt
  have hcop : Nat.Coprime 4 (p ^ (vF p j + 1)) := by
    apply Nat.Coprime.pow_right
    have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)
    have e : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [e]
    exact Nat.Coprime.pow_left 2 h2
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hpN
  have hm' : 4 * m ≡ 1 [MOD p ^ (vF p j + 1)] := by
    unfold Nat.ModEq
    rw [hm, Nat.mod_eq_of_lt hpN]
  have hcong : ∏ l ∈ range j, (4 * l + a) ≡ ∏ l ∈ range j, (4 * (a * m + l))
      [MOD p ^ (vF p j + 1)] := by
    apply Nat.ModEq.prod
    intro l _
    have h1 : 4 * (a * m + l) = a * (4 * m) + 4 * l := by ring
    have h2 : a * (4 * m) ≡ a * 1 [MOD p ^ (vF p j + 1)] := Nat.ModEq.mul_left a hm'
    have h3 := Nat.ModEq.add_right (4 * l) h2
    rw [mul_one] at h3
    rw [h1, add_comm (4 * l) a]
    exact h3.symm
  have hdvd1 : p ^ vF p j ∣ ∏ l ∈ range j, (4 * (a * m + l)) := by
    rw [Finset.prod_mul_distrib, ← Nat.ascFactorial_eq_prod_range]
    apply Dvd.dvd.mul_left
    exact (pow_multiplicity_dvd p (j !)).trans (Nat.factorial_dvd_ascFactorial _ _)
  have hdvd : p ^ vF p j ∣ ∏ l ∈ range j, (4 * l + a) :=
    (hcong.dvd_iff (pow_dvd_pow p (Nat.le_succ _))).mpr hdvd1
  have hne : ∏ l ∈ range j, (4 * l + a) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun l _ => by omega)
  exact (multiplicity_dvd_iff_le hne).mp hdvd

omit hp in
theorem mul_succ_le_pow (hp3 : 3 ≤ p) : ∀ s, 2 ≤ s → s * (p + 1) ≤ p ^ s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => nlinarith
  | succ s hs ih =>
    have h1 : s * (p + 1) * p ≤ p ^ s * p := Nat.mul_le_mul_right p ih
    have h2 : s + 1 ≤ s * p := by nlinarith
    have h3 : (s + 1) * (p + 1) ≤ s * p * (p + 1) := Nat.mul_le_mul_right (p + 1) h2
    have h4 : s * p * (p + 1) = s * (p + 1) * p := by ring
    rw [pow_succ]
    omega

omit hp in
/-- `⌊log_p n⌋ ≤ ⌊n/(p+1)⌋` unless `n = p`. -/
theorem log_le_div (hp3 : 3 ≤ p) {n : ℕ} (hn : n ≠ p) : Nat.log p n ≤ n / (p + 1) := by
  rcases Nat.lt_or_ge n p with hlt | hge
  · rw [Nat.log_eq_zero_iff.mpr (Or.inl hlt)]
    exact Nat.zero_le _
  · have hn0 : n ≠ 0 := by omega
    have hpow := Nat.pow_log_le_self p hn0
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos p)]
    rcases Nat.lt_or_ge (Nat.log p n) 2 with hs | hs
    · have h1 : Nat.log p n ≤ 1 := by omega
      calc Nat.log p n * (p + 1) ≤ 1 * (p + 1) := Nat.mul_le_mul_right _ h1
        _ ≤ n := by omega
    · exact le_trans (mul_succ_le_pow hp3 _ hs) hpow

/-- Lemma 6.1 for `Π₃`: `v_p((2j)!) ≤ v_p(Π₃(j)) + ⌊2j/(p+1)⌋`. -/
theorem vF_two_mul_le (hp3 : 3 ≤ p) (j : ℕ) :
    vF p (2 * j) ≤ 2 * multiplicity p (∏ l ∈ range j, (4 * l + 1)) + 2 * j / (p + 1) := by
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · omega
    · exact h
  have hK := vF_le_two_mul_half (p := p) (2 * j)
  rw [Nat.mul_div_cancel_left j (by norm_num : 0 < 2)] at hK
  have hC := vF_le_multiplicity_prod (p := p) (by omega) (a := 1) Nat.one_pos j
  have hL := log_le_div hp3 (n := 2 * j) (by omega)
  omega

/-- Lemma 6.1 for `Π₁`: `v_p((2j+1)!) ≤ v_p(Π₁(j)) + ⌊(2j+1)/(p+1)⌋`, for `p ≡ 3 (mod 4)`. -/
theorem vF_two_mul_add_one_le (hp4 : p % 4 = 3) (j : ℕ) :
    vF p (2 * j + 1) ≤
      2 * multiplicity p (∏ l ∈ range j, (4 * l + 3)) + (2 * j + 1) / (p + 1) := by
  have hp3 : 3 ≤ p := by omega
  have hne : ∏ l ∈ range j, (4 * l + 3) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun l _ => by omega)
  by_cases h : 2 * j + 1 = p
  · have h1 : vF p (2 * j + 1) = 1 := by
      have h2 := vF_mul (p := p) 1
      rw [mul_one] at h2
      rw [h, h2]
      simp [vF]
    have hmem : (p - 3) / 4 ∈ range j := by
      rw [Finset.mem_range]
      omega
    have hdvd : p ^ 1 ∣ ∏ l ∈ range j, (4 * l + 3) := by
      have h3 : 4 * ((p - 3) / 4) + 3 = p := by omega
      rw [pow_one]
      calc p = 4 * ((p - 3) / 4) + 3 := h3.symm
        _ ∣ ∏ l ∈ range j, (4 * l + 3) := Finset.dvd_prod_of_mem (fun l => 4 * l + 3) hmem
    have h4 : 1 ≤ multiplicity p (∏ l ∈ range j, (4 * l + 3)) :=
      (multiplicity_dvd_iff_le hne).mp hdvd
    rw [h1]
    exact le_trans (by omega) (Nat.le_add_right _ _)
  · have hK := vF_le_two_mul_half (p := p) (2 * j + 1)
    have hj : (2 * j + 1) / 2 = j := by omega
    rw [hj] at hK
    have hC := vF_le_multiplicity_prod (p := p) (by omega) (a := 3) (by norm_num) j
    have hL := log_le_div hp3 h
    omega

/-! ### The sequence `u(n)` -/

/-- `Π₁(N) = ∏_{j=1}^{N} (4j-1)²`. -/
def Pi1 (N : ℕ) : ℕ := ∏ l ∈ range N, (4 * l + 3) ^ 2

/-- `Π₃(N) = ∏_{j=1}^{N} (4j-3)²`. -/
def Pi3 (N : ℕ) : ℕ := ∏ l ∈ range N, (4 * l + 1) ^ 2

/-- Romik's sequence `u(n)`, by the recurrence of Krattenthaler–Müller. -/
def u (n : ℕ) : ℤ :=
  (Pi1 n : ℤ) - ∑ m : Fin n,
    ((2 * n + 1).choose (2 * (m : ℕ) + 1) : ℤ) * (Pi3 (n - m) : ℤ) * u m
termination_by n
decreasing_by exact m.isLt

theorem Pi1_ne_zero (N : ℕ) : Pi1 N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero 2 (by omega))

theorem Pi3_ne_zero (N : ℕ) : Pi3 N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero 2 (by omega))

theorem multiplicity_Pi1 (N : ℕ) :
    multiplicity p (Pi1 N) = 2 * multiplicity p (∏ l ∈ range N, (4 * l + 3)) := by
  unfold Pi1
  rw [Finset.prod_pow, Nat.multiplicity_pow]

theorem multiplicity_Pi3 (N : ℕ) :
    multiplicity p (Pi3 N) = 2 * multiplicity p (∏ l ∈ range N, (4 * l + 1)) := by
  unfold Pi3
  rw [Finset.prod_pow, Nat.multiplicity_pow]

/-! ### `p`-adic norms -/

theorem padicNorm_nat {m : ℕ} (hm : m ≠ 0) :
    padicNorm p (m : ℚ) * (p : ℚ) ^ multiplicity p m = 1 := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  rw [padicNorm.eq_zpow_of_ne_zero hm', padicValRat.of_nat, zpow_neg, zpow_natCast]
  exact inv_mul_cancel₀ (pow_ne_zero _ (p_pos (p := p)).ne')

/-- If `v_p(b) ≤ v_p(a) + c` then `|a/b|_p ≤ p^c`. -/
theorem padicNorm_div_le {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : multiplicity p b ≤ multiplicity p a + c) :
    padicNorm p ((a : ℚ) / (b : ℚ)) ≤ (p : ℚ) ^ c := by
  have hp0 : (0 : ℚ) < p := p_pos
  have hA := padicNorm_nat (p := p) ha
  have hB := padicNorm_nat (p := p) hb
  have hA' : padicNorm p (a : ℚ) = ((p : ℚ) ^ multiplicity p a)⁻¹ := eq_inv_of_mul_eq_one_left hA
  have hB' : padicNorm p (b : ℚ) = ((p : ℚ) ^ multiplicity p b)⁻¹ := eq_inv_of_mul_eq_one_left hB
  rw [padicNorm.div, hA', hB', inv_div_inv, div_le_iff₀ (pow_pos hp0 _), ← pow_add]
  exact pow_le_pow_right₀ one_le_p (by omega)

/-- The normalised coefficient `u(n)/(2n+1)!`. -/
noncomputable def uCoeff (n : ℕ) : ℚ := (u n : ℚ) / ((2 * n + 1)! : ℚ)

theorem uCoeff_eq (n : ℕ) :
    uCoeff n = (Pi1 n : ℚ) / ((2 * n + 1)! : ℚ)
      - ∑ m : Fin n, (Pi3 (n - m) : ℚ) / ((2 * (n - m))! : ℚ) * uCoeff m := by
  unfold uCoeff
  rw [u]
  push_cast
  rw [sub_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : (m : ℕ) < n := m.isLt
  have hle : 2 * (m : ℕ) + 1 ≤ 2 * n + 1 := by omega
  have hch := Nat.choose_mul_factorial_mul_factorial hle
  have hsub : 2 * n + 1 - (2 * (m : ℕ) + 1) = 2 * (n - m) := by omega
  rw [hsub] at hch
  have hq : ((2 * n + 1).choose (2 * (m : ℕ) + 1) : ℚ) * ((2 * (m : ℕ) + 1)! : ℚ)
      * ((2 * (n - m))! : ℚ) = ((2 * n + 1)! : ℚ) := by exact_mod_cast hch
  have h1 : ((2 * (m : ℕ) + 1)! : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have h2 : ((2 * (n - m))! : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have h3 : ((2 * n + 1)! : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have h4 : ((2 * n + 1).choose (2 * (m : ℕ) + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hle).ne'
  rw [← hq]
  field_simp

/-- Theorem 1.5 for `u`: `|u(n)/(2n+1)!|_p ≤ p^⌊(2n+1)/(p+1)⌋`. -/
theorem norm_uCoeff_le (hp4 : p % 4 = 3) (n : ℕ) :
    padicNorm p (uCoeff n) ≤ (p : ℚ) ^ ((2 * n + 1) / (p + 1)) := by
  have hp3 : 3 ≤ p := by omega
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [uCoeff_eq]
    refine le_trans padicNorm.sub (max_le ?_ ?_)
    · apply padicNorm_div_le (Pi1_ne_zero n) (factorial_ne_zero _)
      rw [multiplicity_Pi1]
      exact vF_two_mul_add_one_le hp4 n
    · refine padicNorm.sum_le' (fun m _ => ?_) (by positivity)
      have hm : (m : ℕ) < n := m.isLt
      rw [padicNorm.mul]
      have hA : padicNorm p ((Pi3 (n - m) : ℚ) / ((2 * (n - m))! : ℚ))
          ≤ (p : ℚ) ^ (2 * (n - m) / (p + 1)) := by
        apply padicNorm_div_le (Pi3_ne_zero _) (factorial_ne_zero _)
        rw [multiplicity_Pi3]
        exact vF_two_mul_le hp3 (n - m)
      have hB := ih m hm
      have hexp : 2 * (n - m) / (p + 1) + (2 * (m : ℕ) + 1) / (p + 1) ≤ (2 * n + 1) / (p + 1) := by
        have h := Nat.div_add_div_le_add_div (x := 2 * (n - m)) (y := 2 * (m : ℕ) + 1) (z := p + 1)
        have e : 2 * (n - m) + (2 * (m : ℕ) + 1) = 2 * n + 1 := by omega
        rw [e] at h
        exact h
      calc padicNorm p ((Pi3 (n - m) : ℚ) / ((2 * (n - m))! : ℚ)) * padicNorm p (uCoeff m)
          ≤ (p : ℚ) ^ (2 * (n - m) / (p + 1)) * (p : ℚ) ^ ((2 * (m : ℕ) + 1) / (p + 1)) :=
            mul_le_mul hA hB (padicNorm.nonneg _) (by positivity)
        _ = (p : ℚ) ^ (2 * (n - m) / (p + 1) + (2 * (m : ℕ) + 1) / (p + 1)) := (pow_add _ _ _).symm
        _ ≤ (p : ℚ) ^ ((2 * n + 1) / (p + 1)) := pow_le_pow_right₀ one_le_p hexp

/-- If `⌊(2n+1)/(p+1)⌋ + c ≤ v_p((2n+1)!)` then `p^c ∣ u(n)`. -/
theorem pow_dvd_u (hp4 : p % 4 = 3) {n c : ℕ}
    (h : (2 * n + 1) / (p + 1) + c ≤ vF p (2 * n + 1)) : ((p ^ c : ℕ) : ℤ) ∣ u n := by
  rw [padicNorm.dvd_iff_norm_le]
  have hfac : ((2 * n + 1)! : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have hu : ((u n : ℤ) : ℚ) = uCoeff n * ((2 * n + 1)! : ℚ) := by
    unfold uCoeff
    field_simp
  have hF := padicNorm_factorial (p := p) (2 * n + 1)
  have hF' : padicNorm p ((2 * n + 1)! : ℚ) = ((p : ℚ) ^ vF p (2 * n + 1))⁻¹ :=
    eq_inv_of_mul_eq_one_left hF
  have hp0 : (0 : ℚ) < p := p_pos
  rw [hu, padicNorm.mul, hF', zpow_neg, zpow_natCast, ← div_eq_mul_inv,
    div_le_iff₀ (pow_pos hp0 _), inv_mul_eq_div, le_div_iff₀ (pow_pos hp0 _)]
  calc padicNorm p (uCoeff n) * (p : ℚ) ^ c
      ≤ (p : ℚ) ^ ((2 * n + 1) / (p + 1)) * (p : ℚ) ^ c :=
        mul_le_mul_of_nonneg_right (norm_uCoeff_le hp4 n) (by positivity)
    _ = (p : ℚ) ^ ((2 * n + 1) / (p + 1) + c) := (pow_add _ _ _).symm
    _ ≤ (p : ℚ) ^ vF p (2 * n + 1) := pow_le_pow_right₀ one_le_p h

/-! ### Conjecture 43 -/

/-- **Conjecture 43(1) of Krattenthaler–Müller.** For a prime `p ≡ 3 (mod 4)` and `e ≥ 1`,
`p^(2e-1)` divides `u(n)` whenever `2n + 1 ≥ e p²`, i.e. for `n ≥ ⌈(e p² - 1)/2⌉`. -/
theorem conj43_one (hp4 : p % 4 = 3) {e n : ℕ} (he : 1 ≤ e) (hn : e * p ^ 2 ≤ 2 * n + 1) :
    ((p ^ (2 * e - 1) : ℕ) : ℤ) ∣ u n := by
  apply pow_dvd_u hp4
  have h := bound_odd_power (p := p) hn
  omega

/-- **Conjecture 43(2) of Krattenthaler–Müller.** For a prime `p ≡ 3 (mod 4)` and `e ≥ 2`,
`p^(2e)` divides `u(n)` whenever `2n + 1 ≥ e p² + (e-2) p + 1`, i.e. for
`n ≥ (e p² + (e-2) p)/2`. Here `e = f + 2`. -/
theorem conj43_two (hp4 : p % 4 = 3) {f n : ℕ}
    (hn : (f + 2) * p ^ 2 + f * p + 1 ≤ 2 * n + 1) :
    ((p ^ (2 * (f + 2)) : ℕ) : ℤ) ∣ u n := by
  apply pow_dvd_u hp4
  exact bound_even_power (p := p) (by omega) (by omega) hn

end Romik
