import Mathlib

/-!
# The numbers `τ_n` and the integer inequalities of the paper

For a prime `p`, `vF p n` is the `p`-adic valuation of `n!` and
`tau p n = vF p (p * (n / (p + 1)))`, the number `τ_n` of `paper/romik-valuation.tex`
(Definition 2.1). This file proves the purely arithmetic statements used there:

* `tau_add`, `tau_add_succ`      : Lemma 2.2(a)
* `vF_div_four_add_one_le_tau`   : Lemma 2.2(b)
* `two_mul_div_le`               : Lemma 2.5(a)
* `div_add_le_tau`               : Lemma 2.5(b)
* `verify_valuation`, `verify_dvd_pred` : the inequalities in the proof of Proposition 3.4
* `tau_add_div_sq_le`            : Lemma 5.1

Nothing about elliptic curves or power series is formalised here.
-/

open Nat

namespace Romik

variable {p : ℕ}

/-- The `p`-adic valuation of `n!`. -/
noncomputable def vF (p n : ℕ) : ℕ := multiplicity p n !

/-- `τ_n = v_p((p ⌊n/(p+1)⌋)!)`. -/
noncomputable def tau (p n : ℕ) : ℕ := vF p (p * (n / (p + 1)))

/-- `p² - 1 = (p + 1)(p - 1)` in `ℕ`. -/
theorem sq_sub_one (p : ℕ) (hp : 1 ≤ p) : p ^ 2 - 1 = (p + 1) * (p - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  have h : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
  rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]

/-- Lemma 2.5(a): with `q = ⌊n/(p²-1)⌋` and `m = ⌊n/(p+1)⌋` we have `2q ≤ m`. -/
theorem two_mul_div_le (hp3 : 3 ≤ p) (n : ℕ) : 2 * (n / (p ^ 2 - 1)) ≤ n / (p + 1) := by
  rw [sq_sub_one p (by omega), ← Nat.div_div_eq_div_mul]
  have h := Nat.div_mul_le_self (n / (p + 1)) (p - 1)
  have h2 : n / (p + 1) / (p - 1) * 2 ≤ n / (p + 1) / (p - 1) * (p - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem div_add_one_le (hp3 : 3 ≤ p) {n : ℕ} (hn : p + 2 ≤ n) :
    n / (p ^ 2 - 1) + 1 ≤ n / (p + 1) := by
  have hq := two_mul_div_le hp3 n
  have hm : 1 ≤ n / (p + 1) := Nat.div_pos (by omega) (Nat.succ_pos p)
  omega

section prime

variable [hp : Fact p.Prime]

theorem val_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    multiplicity p a ≤ multiplicity p b :=
  (multiplicity_dvd_iff_le hb).mp ((pow_multiplicity_dvd p a).trans h)

theorem vF_mono {a b : ℕ} (h : a ≤ b) : vF p a ≤ vF p b :=
  val_le_of_dvd (factorial_ne_zero b) (factorial_dvd_factorial h)

theorem vF_add (a b : ℕ) : vF p a + vF p b ≤ vF p (a + b) := by
  unfold vF
  rw [← Nat.multiplicity_mul (factorial_ne_zero a) (factorial_ne_zero b)]
  exact val_le_of_dvd (factorial_ne_zero _) (factorial_mul_factorial_dvd_factorial_add a b)

theorem vF_mul (n : ℕ) : vF p (p * n) = vF p n + n := multiplicity_factorial_mul n

/-- One step of Legendre's formula. -/
theorem vF_div (n : ℕ) : vF p n = n / p + vF p (n / p) := by
  have h : vF p (p * (n / p)) = vF p n := multiplicity_mul_div_factorial n
  have h2 := vF_mul (p := p) (n / p)
  omega

theorem tau_eq (n : ℕ) : tau p n = n / (p + 1) + vF p (n / (p + 1)) := by
  unfold tau
  rw [vF_mul]
  omega

theorem le_tau (n : ℕ) : n / (p + 1) ≤ tau p n := by
  rw [tau_eq]
  omega

/-- Lemma 2.2(a), first part: `τ` is superadditive. -/
theorem tau_add (a b : ℕ) : tau p a + tau p b ≤ tau p (a + b) := by
  unfold tau
  calc vF p (p * (a / (p + 1))) + vF p (p * (b / (p + 1)))
      ≤ vF p (p * (a / (p + 1)) + p * (b / (p + 1))) := vF_add _ _
    _ ≤ vF p (p * ((a + b) / (p + 1))) := by
        apply vF_mono
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left p (Nat.div_add_div_le_add_div)

/-- Lemma 2.2(a), second part: `τ_{n+p+1} ≥ τ_n + 1`. -/
theorem tau_add_succ (n : ℕ) : tau p n + 1 ≤ tau p (n + (p + 1)) := by
  have h : (n + (p + 1)) / (p + 1) = n / (p + 1) + 1 := Nat.add_div_right n (Nat.succ_pos p)
  rw [tau_eq, tau_eq, h]
  have := vF_mono (p := p) (Nat.le_add_right (n / (p + 1)) 1)
  omega

/-- Lemma 2.2(b): `v_p(⌊n/4⌋!) ≤ τ_n - 1` for `n ≥ p + 1`. -/
theorem vF_div_four_add_one_le_tau (hp3 : 3 ≤ p) {n : ℕ} (hn : p + 1 ≤ n) :
    vF p (n / 4) + 1 ≤ tau p n := by
  have hm : 1 ≤ n / (p + 1) := Nat.div_pos hn (Nat.succ_pos p)
  have hτ := le_tau (p := p) n
  rcases Nat.lt_or_ge (n / 4) p with hk | hk
  · have h0 : vF p (n / 4) = 0 :=
      multiplicity_eq_zero_of_not_dvd (fun h => absurd (hp.out.dvd_factorial.mp h) (not_le.mpr hk))
    omega
  · have hk0 : n / 4 ≠ 0 := by omega
    have h1 : (p - 1) * vF p (n / 4) < n / 4 :=
      sub_one_mul_multiplicity_factorial_lt_of_ne_zero p hk0
    have h4 : n / 4 * 4 ≤ n := Nat.div_mul_le_self n 4
    have hlt : n < (p + 1) * (n / (p + 1) + 1) := Nat.lt_mul_div_succ n (Nat.succ_pos p)
    suffices h : vF p (n / 4) + 1 ≤ n / (p + 1) by omega
    by_contra hcon
    have hle : n / (p + 1) ≤ vF p (n / 4) := by omega
    have h2 : (p - 1) * (n / (p + 1)) ≤ (p - 1) * vF p (n / 4) := Nat.mul_le_mul_left _ hle
    have h3 : 2 * (n / (p + 1)) ≤ (p - 1) * (n / (p + 1)) := Nat.mul_le_mul_right _ (by omega)
    have e : (p + 1) * (n / (p + 1) + 1)
        = (p - 1) * (n / (p + 1)) + 2 * (n / (p + 1)) + (p + 1) := by
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega

/-- Lemma 2.5(b): if `n ≥ 4 p^k` with `k ≥ 1`, then `τ_n - ⌊n/(p²-1)⌋ ≥ k + 1`. -/
theorem div_add_le_tau (hp3 : 3 ≤ p) {n k : ℕ} (hk : 1 ≤ k) (hn : 4 * p ^ k ≤ n) :
    n / (p ^ 2 - 1) + k + 1 ≤ tau p n := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hP : 0 < p ^ j := pow_pos hp.out.pos j
  have hm : 3 * p ^ j ≤ n / (p + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos p)]
    have e : p ^ (j + 1) = p ^ j * p := pow_succ p j
    have h3 : p ^ j * 3 ≤ p ^ j * p := Nat.mul_le_mul_left _ hp3
    rw [e] at hn
    nlinarith
  have hv : j ≤ vF p (n / (p + 1)) := by
    apply (multiplicity_dvd_iff_le (factorial_ne_zero _)).mp
    exact dvd_factorial hP (by linarith)
  have hq := two_mul_div_le hp3 n
  rw [tau_eq]
  omega

/-- Proposition 3.4, case `p ∤ n - 1`: `⌊n/(p²-1)⌋ + v_p(n) ≤ τ_n - 1` for `4 ∣ n ≥ p + 2`. -/
theorem verify_valuation (hp3 : 3 ≤ p) {n : ℕ} (hn : p + 2 ≤ n) (h4 : 4 ∣ n) :
    n / (p ^ 2 - 1) + multiplicity p n + 1 ≤ tau p n := by
  rcases Nat.eq_zero_or_pos (multiplicity p n) with h0 | hpos
  · rw [h0]
    have h1 := div_add_one_le hp3 hn
    have h2 := le_tau (p := p) n
    omega
  · apply div_add_le_tau hp3 hpos
    have hdvd : p ^ multiplicity p n ∣ n := pow_multiplicity_dvd p n
    have hcop : Nat.Coprime 4 (p ^ multiplicity p n) := by
      apply Nat.Coprime.pow_right
      have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (by omega)
      have e : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [e]
      exact Nat.Coprime.pow_left 2 h2
    exact Nat.le_of_dvd (by omega) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h4 hdvd)

/-- Proposition 3.4, case `p ∣ n - 1`: for `p ≡ 3 (mod 4)`, `4 ∣ n`, `n ≥ p + 2`,
`1 + ⌊(n-1-p)/(p²-1)⌋ ≤ τ_n - 1`. -/
theorem verify_dvd_pred (hp3 : 3 ≤ p) (hp4 : p % 4 = 3) {n : ℕ} (hn : p + 2 ≤ n)
    (h4 : 4 ∣ n) (hdvd : p ∣ n - 1) : (n - 1 - p) / (p ^ 2 - 1) + 2 ≤ tau p n := by
  obtain ⟨j, hj⟩ := hdvd
  have hnj : n = p * j + 1 := by omega
  have hmod : (p * j + 1) % 4 = 0 := by
    rw [← hnj]
    exact Nat.mod_eq_zero_of_dvd h4
  have hj4 : j % 4 = 1 := by
    have h := Nat.mul_mod p j 4
    rw [hp4] at h
    omega
  have hj5 : 5 ≤ j := by
    by_contra hlt
    have hj1 : j = 1 := by omega
    subst hj1
    omega
  have hn5 : 5 * p + 1 ≤ n := by nlinarith
  have hm : 4 ≤ n / (p + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos p)]
    omega
  have hq := two_mul_div_le hp3 n
  have hq' : (n - 1 - p) / (p ^ 2 - 1) ≤ n / (p ^ 2 - 1) := Nat.div_le_div_right (by omega)
  have h2 := le_tau (p := p) n
  omega

/-- Lemma 5.1: `v_p(A!) - τ_A ≥ ⌊A/p²⌋`. -/
theorem tau_add_div_sq_le (A : ℕ) : tau p A + A / p ^ 2 ≤ vF p A := by
  have hp0 : 0 < p := hp.out.pos
  have h1 : A / (p + 1) + A / (p + 1) / p ≤ A / p := by
    have hA : A / (p + 1) * (p + 1) ≤ A := Nat.div_mul_le_self A (p + 1)
    calc A / (p + 1) + A / (p + 1) / p
        = (p * (A / (p + 1)) + A / (p + 1)) / p := (Nat.mul_add_div hp0 _ _).symm
      _ ≤ A / p := Nat.div_le_div_right (by linarith)
  have h2 : A / (p + 1) / p ≤ A / p / p :=
    Nat.div_le_div_right (le_trans (Nat.le_add_right _ _) h1)
  have e : A / p ^ 2 = A / p / p := by rw [sq, Nat.div_div_eq_div_mul]
  have e1 := vF_div (p := p) (A / (p + 1))
  have e2 := vF_div (p := p) A
  have e3 := vF_div (p := p) (A / p)
  have h3 := vF_mono (p := p) h2
  rw [tau_eq, e]
  omega

/-- Corollary 1.2 in arithmetic form: any `v` with `v_p(A!) ≤ v + τ_A` satisfies `⌊A/p²⌋ ≤ v`. -/
theorem div_sq_le_of_lower_bound {A v : ℕ} (h : vF p A ≤ v + tau p A) : A / p ^ 2 ≤ v := by
  have := tau_add_div_sq_le (p := p) A
  omega

end prime

end Romik
