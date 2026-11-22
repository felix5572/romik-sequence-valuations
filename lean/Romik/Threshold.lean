import Romik.Tau

/-!
# Thresholds for `B(k) = v_p(k!) - ⌊k/(p+1)⌋`

Lemma 6.2 of `paper/romik-valuation.tex`, which turns the bound of Theorem 1.5 for Romik's
sequence `u(n)` into parts (1), (2), (2a) of Conjecture 43 of Krattenthaler–Müller.
Subtraction is avoided: `B(k) ≥ c` is written as `k / (p + 1) + c ≤ vF p k`.
-/

open Nat

namespace Romik

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- With `a = ⌊k/(p+1)⌋` and `b = k mod (p+1)`:  `k = p a + (a + b)`. -/
theorem mul_div_add_eq (p k : ℕ) :
    p * (k / (p + 1)) + (k / (p + 1) + k % (p + 1)) = k := by
  have h := Nat.div_add_mod k (p + 1)
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- `⌊k/p⌋ = a + ⌊(a+b)/p⌋`. -/
theorem div_eq_add (k : ℕ) :
    k / p = k / (p + 1) + (k / (p + 1) + k % (p + 1)) / p := by
  have h2 := Nat.mul_add_div hp.out.pos (k / (p + 1)) (k / (p + 1) + k % (p + 1))
  rw [mul_div_add_eq] at h2
  exact h2

/-- The formula of Lemma 6.2, with the sum over `i ≥ 2` written as `v_p(⌊k/p⌋!)`. -/
theorem vF_eq_add (k : ℕ) :
    vF p k = k / (p + 1) + (k / (p + 1) + k % (p + 1)) / p + vF p (k / p) := by
  have h := vF_div (p := p) k
  have h2 := div_eq_add (p := p) k
  omega

/-- `v_p(⌊k/p⌋!) ≥ e + ⌊e/p⌋` when `k ≥ e p²`. -/
theorem le_vF_div {e k : ℕ} (hk : e * p ^ 2 ≤ k) : e + e / p ≤ vF p (k / p) := by
  have hp0 : 0 < p := hp.out.pos
  have h1 : e ≤ k / p / p := by
    rw [Nat.div_div_eq_div_mul, Nat.le_div_iff_mul_le (Nat.mul_pos hp0 hp0)]
    nlinarith
  have h2 : e / p ≤ k / p / p / p := Nat.div_le_div_right h1
  have h3 := vF_div (p := p) (k / p)
  have h4 := vF_div (p := p) (k / p / p)
  omega

/-- Lemma 6.2(a): `B(k) ≥ 2e - 1` for `k ≥ e p²`. -/
theorem bound_odd_power {e k : ℕ} (hk : e * p ^ 2 ≤ k) :
    k / (p + 1) + 2 * e ≤ vF p k + 1 := by
  have hp0 : 0 < p := hp.out.pos
  have hkey := mul_div_add_eq p k
  -- `a + b ≥ e (p - 1)`, written as `e p ≤ (a + b) + e`
  have hab : e * p ≤ k / (p + 1) + k % (p + 1) + e := by
    by_contra hlt
    have hlt' : k / (p + 1) + k % (p + 1) + e + 1 ≤ e * p := by omega
    have ha : k / (p + 1) + e + 1 ≤ e * p := by omega
    have hmul : p * (k / (p + 1) + e + 1) ≤ p * (e * p) := Nat.mul_le_mul_left p ha
    have e1 : p * (e * p) = e * p ^ 2 := by ring
    have e2 : p * (k / (p + 1) + e + 1) = p * (k / (p + 1)) + e * p + p := by ring
    omega
  have h2 : e ≤ (k / (p + 1) + k % (p + 1)) / p + e / p + 1 := by
    have hadd := Nat.add_div (a := k / (p + 1) + k % (p + 1)) (b := e) hp0
    have hle : e ≤ (k / (p + 1) + k % (p + 1) + e) / p := by
      rw [Nat.le_div_iff_mul_le hp0]
      exact hab
    split_ifs at hadd <;> omega
  have h3 := le_vF_div (p := p) hk
  have h4 := vF_eq_add (p := p) k
  linarith

/-- Lemma 6.2(b): `B(k) ≥ 2e` for odd `k ≥ e p² + (e-2) p + 1`, `e ≥ 2`, `p` odd.
Here `e = f + 2`. -/
theorem bound_even_power (hp2 : p % 2 = 1) {f k : ℕ} (hodd : k % 2 = 1)
    (hk : (f + 2) * p ^ 2 + f * p + 1 ≤ k) : k / (p + 1) + 2 * (f + 2) ≤ vF p k := by
  have hp0 : 0 < p := hp.out.pos
  have hkey := mul_div_add_eq p k
  have hdm := Nat.div_add_mod k (p + 1)
  have e1 : (f + 2) * p ^ 2 = p * ((f + 2) * p) := by ring
  have e2 : (f + 2) * p = f * p + 2 * p := by ring
  have hab : (f + 2) * p ≤ k / (p + 1) + k % (p + 1) := by
    by_contra hlt
    have hlt' : k / (p + 1) + k % (p + 1) + 1 ≤ (f + 2) * p := by omega
    have ha : (f + 2) * p ≤ k / (p + 1) + 1 := by
      by_contra hlt2
      have hlt2' : k / (p + 1) + 2 ≤ (f + 2) * p := by omega
      have hmul : p * (k / (p + 1) + 2) ≤ p * ((f + 2) * p) := Nat.mul_le_mul_left p hlt2'
      have e3 : p * (k / (p + 1) + 2) = p * (k / (p + 1)) + 2 * p := by ring
      omega
    have hb0 : k % (p + 1) = 0 := by omega
    have hkeq : k = (p + 1) * (k / (p + 1)) := by omega
    have heven : (p + 1) % 2 = 0 := by omega
    have hk2 : k % 2 = 0 := by
      rw [hkeq, Nat.mul_mod, heven]
      simp
    omega
  have h1 : f + 2 ≤ (k / (p + 1) + k % (p + 1)) / p := by
    rw [Nat.le_div_iff_mul_le hp0]
    exact hab
  have hk' : (f + 2) * p ^ 2 ≤ k := by omega
  have h3 := le_vF_div (p := p) hk'
  have h4 := vF_eq_add (p := p) k
  linarith [Nat.zero_le ((f + 2) / p)]

/-- Lemma 6.2(c), first part: `B(k) ≥ 2` for `k ≥ p²`. -/
theorem bound_two {k : ℕ} (hk : p ^ 2 ≤ k) : k / (p + 1) + 2 ≤ vF p k := by
  have hp0 : 0 < p := hp.out.pos
  have hkey := mul_div_add_eq p k
  have hab : p ≤ k / (p + 1) + k % (p + 1) := by
    by_contra hlt
    have ha : k / (p + 1) + 1 ≤ p := by omega
    have hmul : p * (k / (p + 1) + 1) ≤ p * p := Nat.mul_le_mul_left p ha
    have e3 : p * (k / (p + 1) + 1) = p * (k / (p + 1)) + p := by ring
    have e4 : p ^ 2 = p * p := sq p
    omega
  have h1 : 1 ≤ (k / (p + 1) + k % (p + 1)) / p := by
    rw [Nat.le_div_iff_mul_le hp0]
    omega
  have hk' : 1 * p ^ 2 ≤ k := by omega
  have h3 := le_vF_div (p := p) hk'
  have h4 := vF_eq_add (p := p) k
  linarith [Nat.zero_le (1 / p)]

/-- Lemma 6.2(c), second part: `B(k) ≥ 1` for odd `k ≥ p² - p + 1`, `p` odd. -/
theorem bound_one (hp2 : p % 2 = 1) {k : ℕ} (hodd : k % 2 = 1) (hk : p ^ 2 + 1 ≤ k + p) :
    k / (p + 1) + 1 ≤ vF p k := by
  have hp0 : 0 < p := hp.out.pos
  have hkey := mul_div_add_eq p k
  have hdm := Nat.div_add_mod k (p + 1)
  have e4 : p ^ 2 = p * p := sq p
  have hab : p ≤ k / (p + 1) + k % (p + 1) := by
    by_contra hlt
    have hlt' : k / (p + 1) + k % (p + 1) + 1 ≤ p := by omega
    have ha : p ≤ k / (p + 1) + 1 := by
      by_contra hlt2
      have hlt2' : k / (p + 1) + 2 ≤ p := by omega
      have hmul : p * (k / (p + 1) + 2) ≤ p * p := Nat.mul_le_mul_left p hlt2'
      have e3 : p * (k / (p + 1) + 2) = p * (k / (p + 1)) + 2 * p := by ring
      omega
    have hb0 : k % (p + 1) = 0 := by omega
    have hkeq : k = (p + 1) * (k / (p + 1)) := by omega
    have heven : (p + 1) % 2 = 0 := by omega
    have hk2 : k % 2 = 0 := by
      rw [hkeq, Nat.mul_mod, heven]
      simp
    omega
  have h1 : 1 ≤ (k / (p + 1) + k % (p + 1)) / p := by
    rw [Nat.le_div_iff_mul_le hp0]
    omega
  have h4 := vF_eq_add (p := p) k
  linarith [Nat.zero_le (vF p (k / p))]

end Romik
