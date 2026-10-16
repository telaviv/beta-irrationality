/-
# Instance I3: the partial-fraction expansion of `R_n` (discharges `Hyp.expansion`)

PROOF_BETA §1–§3 for the concrete `I3.R m` of
`FamilyI3.lean`, with the coefficients `I3.a` of `I3/Concrete/Data.lean` (Taylor coefficients of
`f_k(t₀ + ε)`).

* `R_eq_pfR`: `R m t = (pf m).R t` off the poles (partial-fraction identity, PROOF_BETA §3);
* `pf_symmetric`, `pf_supported`: the data is mirror-symmetric (Lemma 2) and supported in `i ≤ 35`;
* `pf_R2_inner_zero`: `(pf m).R2 l = 0` for integers `-n ≤ l ≤ -1` (triple zeros; used by Lemma C);
* `deriv_deriv_R`: `R'' = (pf m).R2` at natural numbers;
* `expansion_I3`: `L m = ρ + Σ_{j=2}^{18} τ_{2j-2} β(2j)` (Lemma 3 for `R_n`;
  the `expansion` field).

Method: `R m = N/D` for explicit polynomials over `ℚ` (`Npoly`, `Dpoly`), then the general
theory of `Concrete/PartialFrac.lean`.

Status: complete (no `sorry`).
-/
import BetaIrrational.Concrete.PartialFrac
import BetaIrrational.I3.Concrete.Blocks

set_option maxRecDepth 8192

namespace BetaIrr.I3

open Polynomial Finset Filter Topology
open scoped BigOperators

/-- The zero run `[-1040(m+1)-1, 560(m+1)]` (multiplicity 3). -/
def Zset (m : ℕ) : Finset ℤ := Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1))

lemma card_Zset (m : ℕ) : (Zset m).card = 1600 * (m + 1) + 2 := by
  rw [Zset, Int.card_Icc]
  omega

/-- The numerator `(2t + n + 1) Π_l (t - l)^3`. -/
noncomputable def Npoly (m : ℕ) : ℚ[X] :=
  (C 2 * X + C ((nOf m : ℚ) + 1)) * ∏ l ∈ Zset m, (X - C (l : ℚ)) ^ 3

/-- The pole centres `-k - 1/2`. -/
def cen (k : ℕ) : ℚ := -(k : ℚ) - 1 / 2

/-- The denominator `Π_{k ≤ n} (t + k + 1/2)^{B_k}`. -/
noncomputable def Dpoly (m : ℕ) : ℚ[X] := PF.den (range (nOf m + 1)) cen (Bk m)

lemma cen_injOn (s : Set ℕ) : Set.InjOn cen s := fun a _ b _ h => by
  simp only [cen, sub_left_inj, neg_inj, Nat.cast_inj] at h
  exact h

lemma natDegree_Npoly_le (m : ℕ) : (Npoly m).natDegree ≤ 1 + 3 * (1600 * (m + 1) + 2) := by
  unfold Npoly
  refine (natDegree_mul_le).trans (add_le_add natDegree_linear_le ?_)
  refine (natDegree_prod_le _ _).trans ?_
  rw [← card_Zset, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun l _ => natDegree_pow_le.trans ?_)
  rw [natDegree_X_sub_C]

lemma natDegree_Npoly_lt (m : ℕ) : (Npoly m).natDegree < ∑ k ∈ range (nOf m + 1), Bk m k := by
  rw [sum_Bk]
  have := natDegree_Npoly_le m
  omega

lemma aeval_Dpoly (m : ℕ) (t : ℝ) :
    aeval t (Dpoly m) = (blocks.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
        (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod := by
  change _ = (blocks.map (fun b => (∏ k ∈ blk m b, (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod
  rw [prod_blocks, Dpoly, PF.den, map_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  simp only [map_pow, map_sub, aeval_X, aeval_C, eq_ratCast, cen]
  push_cast
  ring

lemma aeval_Npoly (m : ℕ) (t : ℝ) :
    aeval t (Npoly m) = (2 * t + (nOf m : ℝ) + 1) *
      ∏ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)), (t - (l : ℝ)) ^ 3 := by
  simp only [Npoly, Zset, map_mul, map_add, map_prod, map_pow, map_sub, aeval_X, aeval_C,
    eq_ratCast]
  push_cast
  ring

/-- `R m = N / D` everywhere (both sides are `0` at the poles). -/
lemma R_eq_ratfun (m : ℕ) (t : ℝ) : R m t = aeval t (Npoly m) / aeval t (Dpoly m) := by
  rw [R, aeval_Npoly, aeval_Dpoly]

lemma R_eq_ratfun' (m : ℕ) : R m = fun t => aeval t (Npoly m) / aeval t (Dpoly m) :=
  funext (R_eq_ratfun m)

/-! ### The power series side -/

lemma shiftPS_cof (m k : ℕ) :
    PF.shiftPS (cen k) (PF.cof (range (nOf m + 1)) cen (Bk m) k)
      = ∏ k' ∈ (range (nOf m + 1)).erase k,
          (PowerSeries.C ((k' : ℚ) - k) + PowerSeries.X) ^ Bk m k' := by
  unfold PF.cof
  rw [map_prod]
  refine Finset.prod_congr rfl (fun k' _ => ?_)
  rw [map_pow, PF.shiftPS_X_sub_C]
  congr 3
  simp only [cen]
  ring

lemma denSeries_eq (m k : ℕ) :
    denSeries m k = ∏ k' ∈ (range (nOf m + 1)).erase k,
      (PowerSeries.C ((k' : ℚ) - k) + PowerSeries.X)⁻¹ ^ Bk m k' := by
  change (blocks.map (fun b =>
    (∏ k' ∈ (blk m b).erase k, (PowerSeries.C ((k' : ℚ) - k) + PowerSeries.X)⁻¹) ^ b.2)).prod = _
  rw [prod_list_blocks _ (fun b => (blk m b).erase k) ((range (nOf m + 1)).erase k) blocks
    (fun b hb => Finset.erase_subset_erase k (blk_subset m b hb))]
  refine Finset.prod_congr rfl (fun k' hk' => ?_)
  have hne : k' ≠ k := Finset.ne_of_mem_erase hk'
  rw [Bk_eq]
  congr 2
  refine List.map_congr_left (fun b _ => ?_)
  simp [Finset.mem_erase, hne]

lemma denSeries_mul (m k : ℕ) :
    denSeries m k * PF.shiftPS (cen k) (PF.cof (range (nOf m + 1)) cen (Bk m) k) = 1 := by
  rw [denSeries_eq, shiftPS_cof, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun k' hk' => ?_)
  have hne : k' ≠ k := Finset.ne_of_mem_erase hk'
  rw [← mul_pow, PowerSeries.inv_mul_cancel, one_pow]
  simp only [map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero]
  rw [sub_ne_zero]
  exact_mod_cast hne

lemma numSeries_eq (m k : ℕ) : numSeries m k = PF.shiftPS (cen k) (Npoly m) := by
  unfold numSeries Npoly
  rw [map_mul, map_prod]
  congr 1
  · rw [map_add, map_mul, PF.shiftPS_C, PF.shiftPS_X, PF.shiftPS_C,
      show (nOf m : ℚ) - 2 * k = 2 * cen k + ((nOf m : ℚ) + 1) by simp only [cen]; ring,
      map_add, map_mul, map_ofNat]
    ring
  · refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [map_pow, PF.shiftPS_X_sub_C]
    simp only [cen]

lemma fSeries_eq (m k : ℕ) : fSeries m k = PF.shiftPS (cen k) (Npoly m) * denSeries m k := by
  rw [fSeries, numSeries_eq]

/-! ### 1. The partial-fraction identity -/

lemma nonpole_iff (m : ℕ) (t : ℝ) :
    (∀ k ∈ range (nOf m + 1), t ≠ ((cen k : ℚ) : ℝ)) ↔ ∀ k ≤ nOf m, t ≠ -(k : ℝ) - 1 / 2 := by
  have h : ∀ k : ℕ, ((cen k : ℚ) : ℝ) = -(k : ℝ) - 1 / 2 := fun k => by
    simp only [cen]; push_cast; ring
  simp only [Finset.mem_range, Nat.lt_succ_iff, h]

/-- **Partial-fraction identity** (PROOF_BETA §3): off the poles, `R_n` equals the partial-fraction
sum with the Taylor-coefficient data `I3.a`. -/
theorem R_eq_pfR (m : ℕ) (t : ℝ) (ht : ∀ k ≤ nOf m, t ≠ -(k : ℝ) - 1 / 2) :
    R m t = (pf m).R t := by
  rw [R_eq_ratfun, Dpoly, PF.pf_eval' (range (nOf m + 1)) cen (Bk m) (Npoly m) (cen_injOn _)
    (natDegree_Npoly_lt m) (denSeries m) (fun k _ => denSeries_mul m k) t
    ((nonpole_iff m t).mpr ht)]
  unfold PFData.R
  refine Finset.sum_congr rfl (fun k _ => ?_)
  change _ = ∑ i ∈ Icc 1 35, (a m i k : ℝ) * ((t + ((k : ℝ) + 1 / 2)) ^ i)⁻¹
  have hshift : t - ((cen k : ℚ) : ℝ) = t + ((k : ℝ) + 1 / 2) := by
    simp only [cen]; push_cast; ring
  rw [hshift]
  symm
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (Bk_le m k))]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    rw [a, ite_eq_left hi, fSeries_eq]
  · intro i _ hi
    rw [Finset.mem_Icc, not_and_or] at hi
    rw [a, ite_eq_right (by omega), Rat.cast_zero, zero_mul]

/-! ### 2. Support and mirror symmetry -/

theorem pf_supported (m : ℕ) : (pf m).Supported := by
  intro i k hi
  change 35 < i at hi
  change a m i k = 0
  have := Bk_le m k
  rw [a, ite_eq_right (by omega)]

lemma Npoly_mirror (m : ℕ) :
    (Npoly m).comp (C (-((nOf m : ℚ) + 1)) - X) = C (-1) * Npoly m := by
  set α : ℚ := -((nOf m : ℚ) + 1) with hα
  unfold Npoly
  rw [mul_comp]
  have h1 : (C 2 * X + C ((nOf m : ℚ) + 1)).comp (C α - X)
      = C (-1) * (C 2 * X + C ((nOf m : ℚ) + 1)) := by
    rw [add_comp, mul_comp, C_comp, C_comp, X_comp, hα]
    simp only [map_neg, map_add, map_one, map_ofNat]
    ring
  have h2 : (∏ l ∈ Zset m, (X - C (l : ℚ)) ^ 3).comp (C α - X)
      = ∏ l ∈ Zset m, (X - C (l : ℚ)) ^ 3 := by
    change Polynomial.compRingHom (C α - X) _ = _
    rw [map_prod]
    have hfac : ∀ l : ℤ, Polynomial.compRingHom (C α - X) ((X - C (l : ℚ)) ^ 3)
        = -(X - C (((-(nOf m : ℤ) - 1 - l : ℤ)) : ℚ)) ^ 3 := by
      intro l
      rw [map_pow]
      change ((X - C (l : ℚ)).comp (C α - X)) ^ 3 = _
      rw [sub_comp, X_comp, C_comp, ← Odd.neg_pow (by decide)]
      congr 1
      rw [hα]
      push_cast
      simp only [map_sub, map_neg, map_add, map_one, map_natCast]
      ring
    simp only [hfac]
    rw [Finset.prod_neg, card_Zset,
      (show Even (1600 * (m + 1) + 2) from ⟨800 * (m + 1) + 1, by ring⟩).neg_one_pow, one_mul]
    refine Finset.prod_nbij' (fun l => -(nOf m : ℤ) - 1 - l) (fun l => -(nOf m : ℤ) - 1 - l)
      ?_ ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Zset, Finset.mem_Icc, nOf] at hl ⊢
      push_cast at hl ⊢
      omega
    · intro l hl
      simp only [Zset, Finset.mem_Icc, nOf] at hl ⊢
      push_cast at hl ⊢
      omega
    · intro l _
      ring
    · intro l _
      ring
    · intro l _
      rfl
  rw [h1, h2]
  ring

/-- **Lemma 2 data for I3**: `a i (n-k) = (-1)^(i+n) a i k`. -/
theorem pf_symmetric (m : ℕ) : (pf m).Symmetric := by
  intro i k hk
  change k ≤ nOf m at hk
  change a m i (nOf m - k) = (-1) ^ (i + nOf m) * a m i k
  unfold a
  rw [Bk_mirror m k hk]
  split_ifs with h
  swap
  · simp
  rw [fSeries_eq, fSeries_eq]
  have hks : k ∈ range (nOf m + 1) := Finset.mem_range.mpr (by omega)
  have hsym := PF.pf_symm (range (nOf m + 1)) cen (Bk m) (Npoly m) (fun k => nOf m - k)
    (-((nOf m : ℚ) + 1)) (-1)
    (fun k hk => by
      simp only [Finset.mem_range] at hk ⊢
      omega)
    (fun k hk => by
      simp only [Finset.mem_range] at hk
      omega)
    (fun k hk => by
      simp only [Finset.mem_range] at hk
      simp only [cen]
      rw [Nat.cast_sub (by omega)]
      ring)
    (fun k hk => by
      simp only [Finset.mem_range] at hk
      exact Bk_mirror m k (by omega))
    (Npoly_mirror m) (by norm_num) (denSeries m) (fun k _ => denSeries_mul m k) k hks
    (Bk m k - i)
  rw [hsym]
  congr 1
  have hsum := Finset.sum_erase_add (range (nOf m + 1)) (Bk m) hks
  rw [sum_Bk] at hsum
  set E := ∑ k' ∈ (range (nOf m + 1)).erase k, Bk m k'
  rw [show ((-1 : ℚ) * (-1) ^ E * (-1) ^ (Bk m k - i)) = (-1) ^ (1 + E + (Bk m k - i)) by
    rw [pow_add, pow_add, pow_one]]
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := i + nOf m)]
  have hpar : (1 + E + (Bk m k - i)) % 2 = (i + nOf m) % 2 := by
    have hn : nOf m = 480 * (m + 1) := rfl
    rw [hn]
    omega
  rw [hpar]

/-! ### Derivatives -/

/-- `R' = R1` at every non-pole (extends `PFData.hasDerivAt_R`, which assumes `t > -1/2`). -/
lemma hasDerivAt_pfR (P : PFData) (t : ℝ)
    (ht : ∀ k ∈ range (P.K + 1), t + ((k : ℝ) + 1 / 2) ≠ 0) : HasDerivAt P.R (P.R1 t) t :=
  HasDerivAt.fun_sum (fun k hk => HasDerivAt.fun_sum (fun i _ =>
    PFData.hasDerivAt_term (P.a i k) ((k : ℝ) + 1 / 2) t i (ht k hk)))

/-- `R1' = R2` at every non-pole. -/
lemma hasDerivAt_pfR1 (P : PFData) (t : ℝ)
    (ht : ∀ k ∈ range (P.K + 1), t + ((k : ℝ) + 1 / 2) ≠ 0) : HasDerivAt P.R1 (P.R2 t) t :=
  HasDerivAt.fun_sum (fun k hk => HasDerivAt.fun_sum (fun i _ =>
    PFData.hasDerivAt_term1 (P.a i k) ((k : ℝ) + 1 / 2) t i (ht k hk)))

lemma nonpole_of_aeval_ne (m : ℕ) (x : ℝ) (hx : aeval x (Dpoly m) ≠ 0) :
    ∀ k ≤ nOf m, x ≠ -(k : ℝ) - 1 / 2 := by
  intro k hk hxk
  apply hx
  rw [Dpoly, PF.den, map_prod]
  refine Finset.prod_eq_zero (i := k) (Finset.mem_range.mpr (by omega)) ?_
  have h8 := Bk_ge m k hk
  simp only [map_pow, map_sub, aeval_X, aeval_C, eq_ratCast, cen]
  rw [hxk]
  push_cast
  rw [sub_self, zero_pow (by omega)]

lemma pf_shift_ne (m : ℕ) (x : ℝ) (hx : aeval x (Dpoly m) ≠ 0) :
    ∀ k ∈ range ((pf m).K + 1), x + ((k : ℝ) + 1 / 2) ≠ 0 := by
  intro k hk h0
  have hk' : k ≤ nOf m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact nonpole_of_aeval_ne m x hx k hk' (by linarith)

lemma pfR_eq_ratfun (m : ℕ) (x : ℝ) (hx : aeval x (Dpoly m) ≠ 0) :
    (pf m).R x = aeval x (Npoly m) / aeval x (Dpoly m) :=
  (R_eq_pfR m x (nonpole_of_aeval_ne m x hx)).symm.trans (R_eq_ratfun m x)

lemma eventually_aeval_Dpoly_ne (m : ℕ) (t : ℝ) (ht : aeval t (Dpoly m) ≠ 0) :
    ∀ᶠ x in 𝓝 t, aeval x (Dpoly m) ≠ 0 :=
  (Polynomial.continuous_aeval (Dpoly m)).continuousAt.eventually_ne ht

lemma aeval_Dpoly_sq_ne (m : ℕ) (t : ℝ) (ht : aeval t (Dpoly m) ≠ 0) :
    aeval t (Dpoly m ^ 2) ≠ 0 := by
  rw [map_pow]
  exact pow_ne_zero 2 ht

/-- `(pf m).R2 = (N/D)''` at every non-pole. -/
lemma pfR2_eq (m : ℕ) (t : ℝ) (ht : aeval t (Dpoly m) ≠ 0) :
    (pf m).R2 t = aeval t (PF.dnum (PF.dnum (Npoly m) (Dpoly m)) (Dpoly m ^ 2))
      / aeval t ((Dpoly m ^ 2) ^ 2) := by
  have hev := eventually_aeval_Dpoly_ne m t ht
  have h1 : ∀ᶠ x in 𝓝 t, (pf m).R1 x
      = aeval x (PF.dnum (Npoly m) (Dpoly m)) / aeval x (Dpoly m ^ 2) := by
    filter_upwards [hev.eventually_nhds] with x hx
    have hx0 := hx.self_of_nhds
    have hRx : (pf m).R =ᶠ[𝓝 x] fun y => aeval y (Npoly m) / aeval y (Dpoly m) :=
      hx.mono (fun y hy => pfR_eq_ratfun m y hy)
    exact (hasDerivAt_pfR (pf m) x (pf_shift_ne m x hx0)).unique
      ((PF.hasDerivAt_ratfun _ _ x hx0).congr_of_eventuallyEq hRx)
  exact (hasDerivAt_pfR1 (pf m) t (pf_shift_ne m t ht)).unique
    ((PF.hasDerivAt_ratfun _ _ t (aeval_Dpoly_sq_ne m t ht)).congr_of_eventuallyEq h1)

/-- `R_n'' = (N/D)''` at every non-pole. -/
lemma deriv_deriv_R_eq (m : ℕ) (t : ℝ) (ht : aeval t (Dpoly m) ≠ 0) :
    deriv (deriv (R m)) t = aeval t (PF.dnum (PF.dnum (Npoly m) (Dpoly m)) (Dpoly m ^ 2))
      / aeval t ((Dpoly m ^ 2) ^ 2) := by
  rw [R_eq_ratfun']
  have h1 : deriv (fun x => aeval x (Npoly m) / aeval x (Dpoly m)) =ᶠ[𝓝 t]
      fun x => aeval x (PF.dnum (Npoly m) (Dpoly m)) / aeval x (Dpoly m ^ 2) :=
    (eventually_aeval_Dpoly_ne m t ht).mono (fun x hx => (PF.hasDerivAt_ratfun _ _ x hx).deriv)
  rw [h1.deriv_eq]
  exact (PF.hasDerivAt_ratfun _ _ t (aeval_Dpoly_sq_ne m t ht)).deriv

lemma aeval_Dpoly_ne_of_nonpole (m : ℕ) (t : ℝ) (ht : ∀ k ≤ nOf m, t ≠ -(k : ℝ) - 1 / 2) :
    aeval t (Dpoly m) ≠ 0 :=
  PF.aeval_den_ne_zero _ _ _ ((nonpole_iff m t).mpr ht)

/-! ### 4. `R'' = R2` at the natural numbers -/

theorem deriv_deriv_R (m : ℕ) (t : ℕ) : deriv (deriv (R m)) t = (pf m).R2 t := by
  have ht : aeval (t : ℝ) (Dpoly m) ≠ 0 := by
    refine aeval_Dpoly_ne_of_nonpole m t (fun k _ h => ?_)
    have h1 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [deriv_deriv_R_eq m t ht, pfR2_eq m t ht]

/-! ### 3. Triple zeros inside the pole region -/

/-- For `-n ≤ l ≤ -1`, `R_n` has a triple zero at `l`, so `(pf m).R2 l = 0` (used by Lemma C). -/
theorem pf_R2_inner_zero (m : ℕ) (l : ℤ) (h1 : -(nOf m : ℤ) ≤ l) (h2 : l ≤ -1) :
    (pf m).R2 (l : ℝ) = 0 := by
  have ht : aeval (l : ℝ) (Dpoly m) ≠ 0 := by
    refine aeval_Dpoly_ne_of_nonpole m l (fun k _ h => ?_)
    have h' : (2 * l + 2 * k + 1 : ℤ) = 0 := by
      have : (2 * (l : ℝ) + 2 * k + 1) = 0 := by rw [h]; ring
      exact_mod_cast this
    omega
  rw [pfR2_eq m l ht]
  have hl : l ∈ Zset m := by
    simp only [Zset, Finset.mem_Icc, nOf] at h1 ⊢
    push_cast at h1
    omega
  have hN : Npoly m = (X - C (l : ℚ)) ^ 3 *
      ((C 2 * X + C ((nOf m : ℚ) + 1)) * ∏ l' ∈ (Zset m).erase l, (X - C (l' : ℚ)) ^ 3) := by
    unfold Npoly
    rw [← Finset.mul_prod_erase _ _ hl]
    ring
  have h0 := PF.aeval_dnum_dnum_eq_zero (Npoly m) (Dpoly m) _ (l : ℚ) hN
  rw [Rat.cast_intCast] at h0
  rw [h0, zero_div]

/-! ### 5. The `expansion` field of `I3.Hyp` -/

/-- **Lemma 3 for I3** (the `expansion` field of `I3.Hyp`, with `ρ = (pf m).rho` and
`τ m j = (pf m).tau (2j-2)`). -/
theorem expansion_I3 (m : ℕ) :
    L m = ((pf m).rho : ℝ)
      + ∑ j ∈ Icc 2 18, ((pf m).tau (2 * j - 2) : ℝ) * dirichletBeta (2 * j) := by
  rw [L]
  rw [tsum_congr (fun t : ℕ => by rw [deriv_deriv_R m t])]
  exact (pf m).tsum_alt_R2_even (pf_symmetric m) (pf_supported m) 18 (by norm_num [pf])

end BetaIrr.I3
