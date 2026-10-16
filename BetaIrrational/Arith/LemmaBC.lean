/-
# Lemma B, Lemma C and the assembly of ρ, τ (PROOF_BETA §3–§4), for general `PFData`

* `vge_Bq` (**Lemma B**): if `v_p(2m'+1) ≤ λ` for all `m' < k`, then `v_p(B_k^{(j)}) ≥ -jλ`.
* `vge_tau`, `vge_rho`: termwise bounds for `τ_i` and `ρ`.
* `rho_eq_split`: `ρ = -Σ_{l=1}^{K} (-1)^l Σ_{k ≥ l} T(l, k)` with
  `T(l, k) = Σ_i a_{i,k} i(i+1) (k - l + 1/2)^{-(i+2)}` (this is `(R^<_{-l})''(-l)` of PROOF_BETA).
* `vge_rho_of_R2_zero` (**Lemma C**): if `p` is an odd prime with `p > K`, every `a_{i,k}` is
  `p`-integral, and `Σ_{k=0}^{K} T(l, k) = 0` for `1 ≤ l ≤ K` (i.e. `R''(-l) = 0`), then `ρ` is
  `p`-integral.

Status: complete (no `sorry`).
-/
import BetaIrrational.Arith.Valuation
import BetaIrrational.Expansion

set_option linter.unusedSectionVars false

namespace BetaIrr.Arith

open Finset BetaIrr
open BetaIrr.PFData (Bq)

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Small valuation facts -/

theorem padicValRat_two_of_ne (hp2 : p ≠ 2) : padicValRat p 2 = 0 := by
  have : padicValRat p ((2 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    have : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
    simp [padicValNat.eq_zero_of_not_dvd this]
  simpa using this

theorem vge_div_two (hp2 : p ≠ 2) {x : ℚ} {b : ℤ} (h : vge p b x) : vge p b (x / 2) := by
  intro hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  rw [padicValRat.div hx0 two_ne_zero, padicValRat_two_of_ne hp2, sub_zero]
  exact h hx0

theorem padicValRat_int_eq_zero {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : padicValRat p (z : ℚ) = 0 := by
  simp [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd h]

/-- `(z + 1/2)^{-j}` is `p`-integral for odd `p ∤ 2z+1`. -/
theorem vge_inv_half_pow (hp2 : p ≠ 2) {z : ℤ} (h : ¬ (p : ℤ) ∣ 2 * z + 1) (j : ℕ) :
    vge p 0 ((((z : ℚ) + 1 / 2) ^ j)⁻¹) := by
  have he : (z : ℚ) + 1 / 2 = ((2 * z + 1 : ℤ) : ℚ) / 2 := by push_cast; ring
  rw [he, ← inv_pow]
  have h1 : vge p 0 (((((2 * z + 1 : ℤ) : ℚ) / 2))⁻¹) := by
    refine vge_mono (vge_inv (p := p) (b := 0) (le_of_eq ?_)) (by norm_num)
    have hne : ((2 * z + 1 : ℤ) : ℚ) ≠ 0 := by
      have : (2 * z + 1 : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    rw [padicValRat.div hne two_ne_zero, padicValRat_two_of_ne hp2, padicValRat_int_eq_zero h]
    rfl
  simpa using vge_pow h1 j

/-! ### Lemma B -/

/-- **Lemma B.** If `v_p(2m'+1) ≤ λ` for every `m' < k`, then `v_p(B_k^{(j)}) ≥ -jλ`. -/
theorem vge_Bq (j k : ℕ) (lam : ℤ)
    (h : ∀ m' < k, padicValRat p (2 * (m' : ℚ) + 1) ≤ lam) : vge p (-(j * lam)) (Bq j k) := by
  unfold Bq
  refine vge_sum _ _ (fun m' hm' => ?_)
  have hm : m' < k := mem_range.mp hm'
  rw [div_eq_mul_inv, ← inv_pow]
  have h1 := vge_mul (vge_neg_one_pow (p := p) m') (vge_pow (vge_inv (h m' hm)) j)
  simpa using h1

/-! ### Assembly of τ and ρ -/

/-- `τ_i` is bounded by bounds on `a_{i,k} 2^{i+2}`. -/
theorem vge_tau (P : PFData) (i : ℕ) (E : ℤ)
    (h : ∀ k ≤ P.K, vge p E (P.a i k * 2 ^ (i + 2))) : vge p E (P.tau i) := by
  unfold PFData.tau
  refine vge_sum _ _ (fun k hk => ?_)
  have hk' : k ≤ P.K := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have h1 := vge_mul (vge_mul (h k hk') (vge_nat (p := p) (i * (i + 1))))
    (vge_neg_one_pow (p := p) k)
  have he : P.a i k * ((i : ℚ) * (i + 1)) * (-1) ^ k * 2 ^ (i + 2)
      = P.a i k * 2 ^ (i + 2) * ((i * (i + 1) : ℕ) : ℚ) * (-1) ^ k := by push_cast; ring
  rw [he]
  simpa using h1

/-- `ρ` is bounded by bounds on `a_{i,k} 2^{i+2} B_k^{(i+2)}`. -/
theorem vge_rho (P : PFData) (E : ℤ)
    (h : ∀ k ≤ P.K, ∀ i ∈ Icc 1 P.I, vge p E (P.a i k * 2 ^ (i + 2) * Bq (i + 2) k)) :
    vge p E P.rho := by
  unfold PFData.rho
  refine vge_neg (vge_sum _ _ (fun k hk => vge_sum _ _ (fun i hi => ?_)))
  have hk' : k ≤ P.K := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have h1 := vge_mul (vge_mul (h k hk' i hi) (vge_nat (p := p) (i * (i + 1))))
    (vge_neg_one_pow (p := p) k)
  have he : P.a i k * ((i : ℚ) * (i + 1)) * (-1) ^ k * 2 ^ (i + 2) * Bq (i + 2) k
      = P.a i k * 2 ^ (i + 2) * Bq (i + 2) k * ((i * (i + 1) : ℕ) : ℚ) * (-1) ^ k := by
    push_cast; ring
  rw [he]
  simpa using h1

/-! ### Lemma C -/

/-- `T(l, k) = Σ_i a_{i,k} i(i+1) (k - l + 1/2)^{-(i+2)}`: the `k`-th pole's contribution to
`R''(-l)`. -/
def Tlk (P : PFData) (l k : ℕ) : ℚ :=
  ∑ i ∈ Icc 1 P.I, P.a i k * ((i : ℚ) * (i + 1) * ((((k : ℚ) - l + 1 / 2)) ^ (i + 2))⁻¹)

/-- `(-1)^k 2^j B_k^{(j)} = Σ_{l=1}^{k} (-1)^l (k - l + 1/2)^{-j}`. -/
theorem Bq_expand (j k : ℕ) :
    (-1 : ℚ) ^ k * 2 ^ j * Bq j k
      = ∑ l ∈ Icc 1 k, (-1 : ℚ) ^ l * ((((k : ℚ) - l + 1 / 2)) ^ j)⁻¹ := by
  unfold Bq
  rw [mul_sum]
  refine Finset.sum_nbij' (fun m' => k - m') (fun l => k - l) ?_ ?_ ?_ ?_ ?_
  · intro m' hm'; rw [mem_range] at hm'; rw [mem_Icc]; omega
  · intro l hl; rw [mem_Icc] at hl; rw [mem_range]; omega
  · intro m' hm'; rw [mem_range] at hm'; omega
  · intro l hl; rw [mem_Icc] at hl; omega
  · intro m' hm'
    have hm : m' < k := mem_range.mp hm'
    have hcast : ((k - m' : ℕ) : ℚ) = (k : ℚ) - m' := by
      rw [Nat.cast_sub hm.le]
    rw [hcast]
    have hsign : (-1 : ℚ) ^ k = (-1) ^ (k - m') * (-1) ^ m' := by
      rw [← pow_add, Nat.sub_add_cancel hm.le]
    have hsq : ((-1 : ℚ) ^ m') * (-1) ^ m' = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have h2 : (k : ℚ) - ((k : ℚ) - m') + 1 / 2 = (2 * (m' : ℚ) + 1) / 2 := by ring
    rw [h2, hsign, div_pow, inv_div]
    have : (-1 : ℚ) ^ (k - m') * (-1) ^ m' * 2 ^ j * ((-1) ^ m' / (2 * (m' : ℚ) + 1) ^ j)
        = (-1) ^ (k - m') * ((-1) ^ m' * (-1) ^ m') * (2 ^ j / (2 * (m' : ℚ) + 1) ^ j) := by ring
    rw [this, hsq, mul_one]

/-- The splitting identity of Lemma C, step 1. -/
theorem rho_eq_split (P : PFData) :
    P.rho = -∑ l ∈ Icc 1 P.K, (-1 : ℚ) ^ l *
      ∑ k ∈ (range (P.K + 1)).filter (fun k => l ≤ k), Tlk P l k := by
  unfold PFData.rho
  congr 1
  have h1 : ∀ k ∈ range (P.K + 1),
      ∑ i ∈ Icc 1 P.I, P.a i k * ((i : ℚ) * (i + 1)) * (-1) ^ k * 2 ^ (i + 2) * Bq (i + 2) k
        = ∑ l ∈ Icc 1 k, (-1 : ℚ) ^ l * Tlk P l k := by
    intro k _
    simp_rw [Tlk, mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := Bq_expand (i + 2) k
    rw [show P.a i k * ((i : ℚ) * (i + 1)) * (-1) ^ k * 2 ^ (i + 2) * Bq (i + 2) k
        = P.a i k * ((i : ℚ) * (i + 1)) * ((-1) ^ k * 2 ^ (i + 2) * Bq (i + 2) k) by ring,
      this, mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [Finset.sum_congr rfl h1]
  simp_rw [mul_sum]
  refine Finset.sum_comm' (fun k l => ?_)
  simp only [mem_range, mem_Icc, mem_filter]
  omega

/-- **Lemma C.** For an odd prime `p > K` with all `a_{i,k}` `p`-integral: if `R''(-l) = 0` for
`1 ≤ l ≤ K` (in the form `Σ_k T(l,k) = 0`), then `ρ` is `p`-integral. -/
theorem vge_rho_of_R2_zero (P : PFData) (hp2 : p ≠ 2) (hpK : P.K < p)
    (ha : ∀ i k, k ≤ P.K → vge p 0 (P.a i k))
    (hR : ∀ l ∈ Icc 1 P.K, ∑ k ∈ range (P.K + 1), Tlk P l k = 0) : vge p 0 P.rho := by
  rw [rho_eq_split]
  refine vge_neg (vge_sum _ _ (fun l hl => ?_))
  have hl' := mem_Icc.mp hl
  suffices H : vge p 0 (∑ k ∈ (range (P.K + 1)).filter (fun k => l ≤ k), Tlk P l k) by
    simpa using vge_mul (vge_neg_one_pow (p := p) l) H
  -- a term `T(l,k)` is integral when `p ∤ 2(k-l)+1`
  have hT : ∀ k : ℕ, k ≤ P.K → ¬ (p : ℤ) ∣ 2 * ((k : ℤ) - l) + 1 → vge p 0 (Tlk P l k) := by
    intro k hkK hk
    refine vge_sum _ _ (fun i _ => ?_)
    have h1 := vge_inv_half_pow (p := p) hp2 hk (i + 2)
    have h2 := vge_mul (ha i k hkK) (vge_mul (vge_nat (p := p) (i * (i + 1))) h1)
    have he : (((((k : ℤ) - l : ℤ) : ℚ) + 1 / 2) ^ (i + 2))⁻¹
        = ((((k : ℚ) - l + 1 / 2)) ^ (i + 2))⁻¹ := by push_cast; ring
    rw [he] at h2
    simpa using h2
  -- the two singular positions cannot both occur
  have hpd : ∀ k₁ k₂ : ℕ, k₁ ≤ P.K → k₂ < l → l ≤ k₁ →
      (p : ℤ) ∣ 2 * ((k₁ : ℤ) - l) + 1 → (p : ℤ) ∣ 2 * ((k₂ : ℤ) - l) + 1 → False := by
    intro k₁ k₂ hk₁ hk₂ hlk h₁ h₂
    have h3 : (p : ℤ) ∣ 2 * ((k₁ : ℤ) - k₂) := by
      have := dvd_sub h₁ h₂
      have he : 2 * ((k₁ : ℤ) - l) + 1 - (2 * ((k₂ : ℤ) - l) + 1) = 2 * ((k₁ : ℤ) - k₂) := by
        ring
      rwa [he] at this
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    rcases hpz.dvd_or_dvd h3 with h4 | h4
    · have : p ∣ 2 := by exact_mod_cast h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
    · have hpos : (0 : ℤ) < (k₁ : ℤ) - k₂ := by omega
      have := Int.le_of_dvd hpos h4
      omega
  set Lft := (range (P.K + 1)).filter (fun k => l ≤ k)
  set Rgt := (range (P.K + 1)).filter (fun k => ¬ l ≤ k)
  have hsplit : ∑ k ∈ Lft, Tlk P l k + ∑ k ∈ Rgt, Tlk P l k = 0 := by
    exact (sum_filter_add_sum_filter_not _ _ _).trans (hR l hl)
  by_cases hsing : ∃ k₁ ∈ Lft, (p : ℤ) ∣ 2 * ((k₁ : ℤ) - l) + 1
  · obtain ⟨k₁, hk₁, hd₁⟩ := hsing
    have hk₁' := mem_filter.mp hk₁
    have hRgt : vge p 0 (∑ k ∈ Rgt, Tlk P l k) := by
      have hRK : ∀ k ∈ Rgt, k ≤ P.K := fun k hk =>
        Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hk).1)
      refine vge_sum _ _ (fun k hk => hT k (hRK k hk) (fun hd => ?_))
      have hk' := mem_filter.mp hk
      exact hpd k₁ k (Nat.lt_succ_iff.mp (mem_range.mp hk₁'.1)) (by omega) hk₁'.2 hd₁ hd
    have : ∑ k ∈ Lft, Tlk P l k = -∑ k ∈ Rgt, Tlk P l k := by linarith
    rw [this]; exact vge_neg hRgt
  · push Not at hsing
    exact vge_sum _ _ (fun k hk => hT k
      (Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hk).1)) (hsing k hk))

end BetaIrr.Arith
