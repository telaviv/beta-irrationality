/-
# Expansion lemmas (PROOF_BETA §2: Lemmas 1–3)

We work with *partial-fraction data*: rational coefficients `a i k` of `(t + k + 1/2)^(-i)`,
for `1 ≤ i ≤ I` and `0 ≤ k ≤ K`. The rational function is
`R t = ∑ₖ ∑ᵢ a i k / (t + k + 1/2)^i`.

* `hasDerivAt_R`, `hasDerivAt_R1` (Lemma 1, derivative part): `R'' = R2` termwise for `t > -1/2`.
* `tsum_alt_shift` (Lemma 1, series part):
  `∑_{t≥0} (-1)^t (t+k+1/2)^(-j) = (-1)^k 2^j (β(j) - B_k^{(j)})`.
* `tsum_alt_R2` (Lemma 1): `∑_{t≥0} (-1)^t R''(t) = ρ + ∑_{i=1}^{I} τ_i β(i+2)` with `ρ, τ_i ∈ ℚ`.
* `tau_eq_zero_of_odd` (Lemma 2): under the symmetry `a i (K-k) = (-1)^(i+K) a i k`,
  `τ_i = 0` for odd `i`.
* `tsum_alt_R2_even` (Lemma 3): hence `∑ (-1)^t R''(t) = ρ + ∑_{j=2}^{J} τ_{2j-2} β(2j)`.
  `β(2)` never occurs.

Status: complete (no `sorry`).
-/
import BetaIrrational.Defs

namespace BetaIrr

open Finset
open scoped BigOperators

/-- Partial-fraction data: coefficients `a i k` of `(t + k + 1/2)^(-i)`,
`1 ≤ i ≤ I`, `0 ≤ k ≤ K`. -/
structure PFData where
  I : ℕ
  K : ℕ
  a : ℕ → ℕ → ℚ

namespace PFData

variable (P : PFData)

/-- `R t = ∑ₖ ∑ᵢ a i k (t + k + 1/2)^(-i)`. -/
noncomputable def R (t : ℝ) : ℝ :=
  ∑ k ∈ range (P.K + 1), ∑ i ∈ Icc 1 P.I, (P.a i k : ℝ) * ((t + ((k : ℝ) + 1 / 2)) ^ i)⁻¹

/-- The termwise first derivative. -/
noncomputable def R1 (t : ℝ) : ℝ :=
  ∑ k ∈ range (P.K + 1), ∑ i ∈ Icc 1 P.I,
    (P.a i k : ℝ) * (-(i : ℝ) * ((t + ((k : ℝ) + 1 / 2)) ^ (i + 1))⁻¹)

/-- The termwise second derivative `R'' t = ∑ₖ ∑ᵢ a i k · i(i+1) (t + k + 1/2)^(-(i+2))`. -/
noncomputable def R2 (t : ℝ) : ℝ :=
  ∑ k ∈ range (P.K + 1), ∑ i ∈ Icc 1 P.I,
    (P.a i k : ℝ) * ((i : ℝ) * (i + 1) * ((t + ((k : ℝ) + 1 / 2)) ^ (i + 2))⁻¹)

/-! ### Lemma 1, derivative part -/

/-- `d/dt (t + c)^(-i) = -i (t + c)^(-(i+1))` where `t + c ≠ 0`. -/
lemma hasDerivAt_inv_pow (c t : ℝ) (i : ℕ) (h : t + c ≠ 0) :
    HasDerivAt (fun t => ((t + c) ^ i)⁻¹) (-(i : ℝ) * ((t + c) ^ (i + 1))⁻¹) t := by
  have h1 : HasDerivAt (fun t => t + c) 1 t := (hasDerivAt_id t).add_const c
  have h2 := (h1.fun_pow i).inv (pow_ne_zero i h)
  refine h2.congr_deriv ?_
  rcases i with _ | m
  · simp
  · rw [Nat.add_sub_cancel]
    field_simp
    ring

lemma hasDerivAt_term (a c t : ℝ) (i : ℕ) (h : t + c ≠ 0) :
    HasDerivAt (fun t => a * ((t + c) ^ i)⁻¹) (a * (-(i : ℝ) * ((t + c) ^ (i + 1))⁻¹)) t :=
  (hasDerivAt_inv_pow c t i h).const_mul a

lemma hasDerivAt_term1 (a c t : ℝ) (i : ℕ) (h : t + c ≠ 0) :
    HasDerivAt (fun t => a * (-(i : ℝ) * ((t + c) ^ (i + 1))⁻¹))
      (a * ((i : ℝ) * (i + 1) * ((t + c) ^ (i + 2))⁻¹)) t := by
  have h' := ((hasDerivAt_inv_pow c t (i + 1) h).const_mul (-(i : ℝ))).const_mul a
  refine h'.congr_deriv ?_
  push_cast
  ring

lemma shift_ne_zero (t : ℝ) (ht : -1 / 2 < t) (k : ℕ) : t + ((k : ℝ) + 1 / 2) ≠ 0 := by
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact ne_of_gt (by linarith)

/-- **Lemma 1 (derivative part).** `R' = R1` on `t > -1/2`. -/
lemma hasDerivAt_R (t : ℝ) (ht : -1 / 2 < t) : HasDerivAt P.R (P.R1 t) t :=
  HasDerivAt.fun_sum (fun k _ => HasDerivAt.fun_sum (fun i _ =>
    hasDerivAt_term (P.a i k) ((k : ℝ) + 1 / 2) t i (shift_ne_zero t ht k)))

/-- **Lemma 1 (derivative part).** `R1' = R2` on `t > -1/2`, so `R'' = R2`. -/
lemma hasDerivAt_R1 (t : ℝ) (ht : -1 / 2 < t) : HasDerivAt P.R1 (P.R2 t) t :=
  HasDerivAt.fun_sum (fun k _ => HasDerivAt.fun_sum (fun i _ =>
    hasDerivAt_term1 (P.a i k) ((k : ℝ) + 1 / 2) t i (shift_ne_zero t ht k)))

/-! ### Lemma 1, series part -/

/-- The rational partial sums `B_k^{(j)} = ∑_{m<k} (-1)^m / (2m+1)^j`. -/
def Bq (j k : ℕ) : ℚ := ∑ m ∈ range k, (-1 : ℚ) ^ m / (2 * (m : ℚ) + 1) ^ j

lemma Bq_cast (j k : ℕ) : (Bq j k : ℝ) = ∑ m ∈ range k, betaTerm j m := by
  simp [Bq, betaTerm]

lemma alt_term_eq (j k t : ℕ) :
    (-1 : ℝ) ^ t * (((t : ℝ) + ((k : ℝ) + 1 / 2)) ^ j)⁻¹
      = (-1) ^ k * 2 ^ j * betaTerm j (t + k) := by
  have hpos : (0 : ℝ) < (t : ℝ) + ((k : ℝ) + 1 / 2) := by positivity
  have h2 : (2 : ℝ) * ((t + k : ℕ) : ℝ) + 1 = 2 * ((t : ℝ) + ((k : ℝ) + 1 / 2)) := by
    push_cast; ring
  rw [betaTerm, h2, mul_pow, pow_add]
  have hk : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  field_simp
  linear_combination -hk

lemma summable_alt (j k : ℕ) (hj : 2 ≤ j) :
    Summable (fun t : ℕ => (-1 : ℝ) ^ t * (((t : ℝ) + ((k : ℝ) + 1 / 2)) ^ j)⁻¹) := by
  have hs : Summable (fun t : ℕ => betaTerm j (t + k)) :=
    (summable_nat_add_iff k).mpr (summable_betaTerm hj)
  have := hs.mul_left ((-1 : ℝ) ^ k * 2 ^ j)
  refine this.congr (fun t => ?_)
  rw [alt_term_eq]

/-- **Lemma 1 (series identity).** For `j ≥ 2`,
`∑_{t≥0} (-1)^t (t + k + 1/2)^(-j) = (-1)^k 2^j (β(j) - B_k^{(j)})`. -/
theorem tsum_alt_shift (j k : ℕ) (hj : 2 ≤ j) :
    ∑' t : ℕ, (-1 : ℝ) ^ t * (((t : ℝ) + ((k : ℝ) + 1 / 2)) ^ j)⁻¹
      = (-1) ^ k * 2 ^ j * (dirichletBeta j - (Bq j k : ℝ)) := by
  have hs : Summable (fun t : ℕ => betaTerm j (t + k)) :=
    (summable_nat_add_iff k).mpr (summable_betaTerm hj)
  have hsplit := (summable_betaTerm hj).sum_add_tsum_nat_add k
  calc ∑' t : ℕ, (-1 : ℝ) ^ t * (((t : ℝ) + ((k : ℝ) + 1 / 2)) ^ j)⁻¹
      = ∑' t : ℕ, (-1 : ℝ) ^ k * 2 ^ j * betaTerm j (t + k) := by
        congr 1; ext t; exact alt_term_eq j k t
    _ = (-1) ^ k * 2 ^ j * ∑' t : ℕ, betaTerm j (t + k) := hs.tsum_mul_left _
    _ = (-1) ^ k * 2 ^ j * (dirichletBeta j - (Bq j k : ℝ)) := by
        rw [Bq_cast, dirichletBeta, ← hsplit]
        ring

/-! ### Lemma 1: the full expansion -/

/-- `τ_i = ∑ₖ a i k · i(i+1) · (-1)^k · 2^(i+2)`: the coefficient of `β(i+2)`. -/
def tau (i : ℕ) : ℚ :=
  ∑ k ∈ range (P.K + 1), P.a i k * ((i : ℚ) * (i + 1)) * (-1) ^ k * 2 ^ (i + 2)

/-- `ρ = -∑ₖ ∑ᵢ a i k · i(i+1) · (-1)^k · 2^(i+2) · B_k^{(i+2)}`: the rational part. -/
def rho : ℚ :=
  -∑ k ∈ range (P.K + 1), ∑ i ∈ Icc 1 P.I,
    P.a i k * ((i : ℚ) * (i + 1)) * (-1) ^ k * 2 ^ (i + 2) * Bq (i + 2) k

/-- **Lemma 1.** `∑_{t≥0} (-1)^t R''(t) = ρ + ∑_{i=1}^{I} τ_i β(i+2)`. -/
theorem tsum_alt_R2 :
    ∑' t : ℕ, (-1 : ℝ) ^ t * P.R2 t
      = (P.rho : ℝ) + ∑ i ∈ Icc 1 P.I, (P.tau i : ℝ) * dirichletBeta (i + 2) := by
  -- distribute (-1)^t and exchange the finite sums with the tsum
  have hterm : ∀ t : ℕ, (-1 : ℝ) ^ t * P.R2 t
      = ∑ k ∈ range (P.K + 1), ∑ i ∈ Icc 1 P.I,
          (P.a i k : ℝ) * ((i : ℝ) * (i + 1)) *
            ((-1 : ℝ) ^ t * (((t : ℝ) + ((k : ℝ) + 1 / 2)) ^ (i + 2))⁻¹) := by
    intro t
    rw [R2, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simp_rw [hterm]
  have hsum_i : ∀ k ∈ range (P.K + 1), ∀ i ∈ Icc 1 P.I, Summable (fun t : ℕ =>
      (P.a i k : ℝ) * ((i : ℝ) * (i + 1)) *
        ((-1 : ℝ) ^ t * (((t : ℝ) + ((k : ℝ) + 1 / 2)) ^ (i + 2))⁻¹)) :=
    fun k _ i _ => (summable_alt (i + 2) k (by omega)).mul_left _
  rw [Summable.tsum_finsetSum (fun k hk => summable_sum (fun i hi => hsum_i k hk i hi))]
  have hinner : ∀ k ∈ range (P.K + 1),
      ∑' t : ℕ, ∑ i ∈ Icc 1 P.I, (P.a i k : ℝ) * ((i : ℝ) * (i + 1)) *
          ((-1 : ℝ) ^ t * (((t : ℝ) + ((k : ℝ) + 1 / 2)) ^ (i + 2))⁻¹)
        = ∑ i ∈ Icc 1 P.I, (P.a i k : ℝ) * ((i : ℝ) * (i + 1)) *
            ((-1) ^ k * 2 ^ (i + 2) * (dirichletBeta (i + 2) - (Bq (i + 2) k : ℝ))) := by
    intro k hk
    rw [Summable.tsum_finsetSum (fun i hi => hsum_i k hk i hi)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(summable_alt (i + 2) k (by omega)).tsum_mul_left, tsum_alt_shift (i + 2) k (by omega)]
  rw [Finset.sum_congr rfl hinner]
  -- rearrange into ρ + ∑ τ_i β(i+2)
  simp only [rho, tau, Rat.cast_neg, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_add, Finset.sum_mul]
  rw [Finset.sum_comm (s := Icc 1 P.I)]
  rw [neg_add_eq_sub, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ### Lemma 2: symmetry kills the odd τ -/

/-- The mirror symmetry `t ↦ -K-1-t` of `PROOF_BETA` Lemma 2, at the level of the data. -/
def Symmetric : Prop :=
  ∀ i k, k ≤ P.K → P.a i (P.K - k) = (-1) ^ (i + P.K) * P.a i k

/-- **Lemma 2.** Under the symmetry, `τ_i = 0` for odd `i`. -/
theorem tau_eq_zero_of_odd (hsym : P.Symmetric) {i : ℕ} (hi : Odd i) : P.tau i = 0 := by
  set S := ∑ k ∈ range (P.K + 1), (-1 : ℚ) ^ k * P.a i k with hS
  have h := Finset.sum_range_reflect (fun k => (-1 : ℚ) ^ k * P.a i k) (P.K + 1)
  simp only [add_tsub_cancel_right] at h
  have hrefl : S = -S := by
    calc S = ∑ k ∈ range (P.K + 1), (-1 : ℚ) ^ (P.K - k) * P.a i (P.K - k) := by
          rw [hS]; exact h.symm
      _ = ∑ k ∈ range (P.K + 1), -((-1 : ℚ) ^ k * P.a i k) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hk : k ≤ P.K := by simpa [Nat.lt_succ_iff] using hk
          rw [hsym i k hk]
          have hk2 : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by
            rw [← pow_add, ← two_mul, pow_mul]; norm_num
          have hpow : ((-1 : ℚ) ^ (P.K - k)) = (-1) ^ P.K * (-1) ^ k := by
            have : (-1 : ℚ) ^ (P.K - k) * (-1) ^ k = (-1) ^ P.K := by
              rw [← pow_add, Nat.sub_add_cancel hk]
            calc (-1 : ℚ) ^ (P.K - k) = (-1) ^ (P.K - k) * ((-1) ^ k * (-1) ^ k) := by
                  rw [hk2, mul_one]
              _ = (-1) ^ P.K * (-1) ^ k := by rw [← mul_assoc, this]
          rw [hpow, pow_add, hi.neg_one_pow]
          have hK2 : ((-1 : ℚ) ^ P.K) * (-1) ^ P.K = 1 := by
            rw [← pow_add, ← two_mul, pow_mul]; norm_num
          linear_combination (-(P.a i k) * (-1) ^ k) * hK2
      _ = -S := by rw [Finset.sum_neg_distrib, hS]
  have hS0 : S = 0 := by linarith
  have : P.tau i = ((i : ℚ) * (i + 1)) * 2 ^ (i + 2) * S := by
    rw [tau, hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [this, hS0, mul_zero]

/-! ### Lemma 3: only β(4), β(6), …, β(2J) occur -/

/-- `a i k = 0` for `i > I`: the data is supported in `1 ≤ i ≤ I`. -/
def Supported : Prop := ∀ i k, P.I < i → P.a i k = 0

lemma tau_eq_zero_of_gt (hsupp : P.Supported) {i : ℕ} (hi : P.I < i) : P.tau i = 0 := by
  simp [tau, hsupp i _ hi]

/-- **Lemma 3.** For symmetric data supported in `1 ≤ i ≤ I ≤ 2J - 1` (an odd top index `I = 2J-1`
is allowed: its `τ` vanishes by symmetry):
`∑_{t≥0} (-1)^t R''(t) = ρ + ∑_{j=2}^{J} τ_{2j-2} β(2j)`. In particular `β(2)` does not occur. -/
theorem tsum_alt_R2_even (hsym : P.Symmetric) (hsupp : P.Supported) (J : ℕ)
    (hIJ : P.I + 1 ≤ 2 * J) :
    ∑' t : ℕ, (-1 : ℝ) ^ t * P.R2 t
      = (P.rho : ℝ) + ∑ j ∈ Icc 2 J, (P.tau (2 * j - 2) : ℝ) * dirichletBeta (2 * j) := by
  rw [tsum_alt_R2]
  congr 1
  set g : ℕ → ℝ := fun i => (P.tau i : ℝ) * dirichletBeta (i + 2) with hg
  -- extend the range to `Icc 1 (2J-1)` (the extra terms vanish by support)
  have hext : ∑ i ∈ Icc 1 P.I, g i = ∑ i ∈ Icc 1 (2 * J - 1), g i := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) (fun i hi hni => ?_)
    have : P.I < i := by simp only [Finset.mem_Icc] at hi hni; omega
    simp [hg, tau_eq_zero_of_gt P hsupp this]
  rw [hext]
  -- drop the odd indices
  have hodd : ∑ i ∈ Icc 1 (2 * J - 1) with Even i, g i = ∑ i ∈ Icc 1 (2 * J - 1), g i := by
    refine Finset.sum_filter_of_ne (fun i _ hne => ?_)
    by_contra hev
    have hodd : Odd i := Nat.not_even_iff_odd.mp hev
    exact hne (by simp [hg, tau_eq_zero_of_odd P hsym hodd])
  rw [← hodd]
  -- reindex the even indices `i = 2j - 2`, `2 ≤ j ≤ J`
  have himg : (Icc 1 (2 * J - 1)).filter Even = (Icc 2 J).image (fun j => 2 * j - 2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨m, hm⟩⟩
      exact ⟨m + 1, by omega, by omega⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨j - 1, by omega⟩⟩
  rw [himg, Finset.sum_image (fun j1 hj1 j2 hj2 h => by
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj1 hj2
    have h' : 2 * j1 - 2 = 2 * j2 - 2 := h
    omega)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_Icc] at hj
  simp only [hg]
  congr 2
  omega

end PFData

end BetaIrr
