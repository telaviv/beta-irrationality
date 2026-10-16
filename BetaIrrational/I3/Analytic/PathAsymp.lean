/-
# Stirling along the contour (PROOF_BETA100 §6.4–6.5)

For `x` in the sector region (`‖α_i(x)‖ ≥ a`, `|arg α_i(x)| ≤ π - η`, `α_i(x) = s_i x + u_i`)
and `n = 480(m+1) ≥ 4/a`:

* `Pfun_asymp` (6.4.1): `P_n(nx) = n(2x + 1 + 1/n) exp(λ_n + nΨ(x) + ψ₀(x) + e)`,
  `|e| ≤ 76 (9 + 1/(6 sin²(η/2)))/(a n)`, with `λ_n = -G n log n + G n - 29 log n + 3 log 2π`;
* `mu_asymp`, `mu1_bound` (6.4.3): `|μ(nx) - Ψ'(x)| ≤ …/n`, `|μ'(nx)| ≤ …/n` (for `Re x ≥ 0`);
* `q_mul_Hn`: the exact identity
  `q H_n = ¼[(-1 + 2q - q²)(μ² + μ') + 6πiμ(1 - q²) + 3π²(3 + 2q + 3q²)]`, `q = e^{2πiz}`,
  which gives both the bound (U) and the main-term form (M).

Here `Ψ(x) = Σ c_i α_i log α_i`, `Ψ'(x) = Σ c_i s_i log α_i`, `ψ₀(x) = Σ c_i (β_i - 1/2) log α_i`.

Mirrors `Analytic/PathAsymp.lean` (instance I3); the definitions `alphaI`, `PsiI`, …, `lamN`,
`SectorAt` are in `Factors.lean`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.LogDeriv
import BetaIrrational.Analytic.StirlingSum

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real Finset Filter Topology
open BetaIrr.Analytic BetaIrr.Fam.Analytic


lemma Gi_scaled (m : ℕ) (i : Fin 58) (x : ℂ) (n : ℝ) (hn : n = (I3.nOf m : ℝ)) :
    Gi m i ((n : ℂ) * x) = (n : ℂ) * alphaI i x + βI i := by
  unfold Gi alphaI; rw [hn]; push_cast; ring

lemma sum_cs_C : ∑ i, (cI i : ℂ) * sI i = 0 := by
  have := congrArg (fun r : ℝ => (r : ℂ)) sum_cs; push_cast at this; exact this

lemma sum_cu_C : ∑ i, (cI i : ℂ) * uI i = -(179 / 10) := by
  have := congrArg (fun r : ℝ => (r : ℂ)) sum_cu; push_cast at this; exact this

lemma sum_cβ_C : ∑ i, (cI i : ℂ) * ((βI i : ℂ) - 1 / 2) = -29 := by
  have := congrArg (fun r : ℝ => (r : ℂ)) sum_cβ; push_cast at this; exact this

lemma sum_c_C : ∑ i, (cI i : ℂ) = 6 := by
  have := congrArg (fun r : ℝ => (r : ℂ)) sum_c; push_cast at this; exact this

lemma sum_c_alpha (x : ℂ) : ∑ i, (cI i : ℂ) * alphaI i x = -(179 / 10) := by
  unfold alphaI
  simp only [mul_add, sum_add_distrib]
  rw [sum_cu_C]
  have : ∑ i, (cI i : ℂ) * (sI i * x) = (∑ i, (cI i : ℂ) * sI i) * x := by
    rw [sum_mul]; exact sum_congr rfl (fun i _ => by ring)
  rw [this, sum_cs_C]; ring

lemma sectorHyp_of (a η : ℝ) (x : ℂ) (h : SectorAt a η x) :
    SectorHyp univ (fun i => alphaI i x) βI η a :=
  fun i _ => ⟨(h i).1, (h i).2, (βI_pos i).1, (βI_pos i).2⟩

/-- **(6.4.1)** Stirling for `P_n` along the contour. -/
theorem Pfun_asymp (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hx : SectorAt a η x) (hn : 4 / a ≤ (I3.nOf m : ℝ)) :
    ∃ e : ℂ, ‖e‖ ≤ 76 * ((9 + 1 / (6 * Real.sin (η / 2) ^ 2)) / (a * I3.nOf m)) ∧
      Pfun m ((I3.nOf m : ℝ) * x) = ((I3.nOf m : ℝ) : ℂ) * (2 * x + 1 + 1 / (I3.nOf m : ℝ)) *
        Complex.exp (lamN (I3.nOf m) + (I3.nOf m : ℝ) * PsiI x + psi0I x + e) := by
  set n : ℝ := (I3.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hS := sectorHyp_of a η x hx
  have hprod := prod_Gamma_zpow_eq_exp univ cI (fun i => alphaI i x) βI hη0 hη ha hS hn
  have hbound := norm_sum_logGamma_sub_main_le univ cI (fun i => alphaI i x) βI hη0 hη ha hS hn
  have hmain := sum_main_eq univ cI (fun i => alphaI i x) βI n
  set e := ∑ i, (cI i : ℂ) * (Stirling.logGammaS (n * alphaI i x + βI i)
    - mainTerm n (alphaI i x) (βI i)) with he
  refine ⟨e, ?_, ?_⟩
  · rw [sum_abs_c] at hbound; exact hbound
  have hsplit : ∑ i, (cI i : ℂ) * Stirling.logGammaS (n * alphaI i x + βI i)
      = ∑ i, (cI i : ℂ) * mainTerm n (alphaI i x) (βI i) + e := by
    rw [he, ← sum_add_distrib]; exact sum_congr rfl (fun i _ => by ring)
  have hcβ := sum_cβ_C
  have hc := sum_c_C
  have hca := sum_c_alpha x
  have hΨ : ∑ i, (cI i : ℂ) * (alphaI i x * Complex.log (alphaI i x) - alphaI i x)
      = PsiI x + 179 / 10 := by
    rw [show (∑ i, (cI i : ℂ) * (alphaI i x * Complex.log (alphaI i x) - alphaI i x))
        = PsiI x - ∑ i, (cI i : ℂ) * alphaI i x by
      unfold PsiI; rw [← sum_sub_distrib]; exact sum_congr rfl (fun i _ => by ring), hca]
    ring
  have hψ : ∑ i, (cI i : ℂ) * (βI i - 1 / 2) * Complex.log (alphaI i x) = psi0I x := rfl
  have hP : Pfun m ((n : ℂ) * x) = (2 * ((n : ℂ) * x) + n + 1) *
      ∏ i, Complex.Gamma ((n : ℂ) * alphaI i x + βI i) ^ cI i := by
    unfold Pfun
    congr 1
    exact prod_congr rfl (fun i _ => by
      rw [show (sI i : ℂ) * ((n : ℂ) * x) + (I3.nOf m : ℂ) * uI i + βI i
        = (n : ℂ) * alphaI i x + βI i by unfold alphaI; rw [hn_def]; push_cast; ring])
  rw [hP, hprod, hsplit, hmain, hca, hcβ, hc, hΨ, hψ]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  rw [show (2 * ((n : ℂ) * x) + n + 1) = (n : ℂ) * (2 * x + 1 + 1 / n) by field_simp]
  congr 2
  unfold lamN
  push_cast
  ring

/-- `‖2nx + n + 1‖ ≥ n` for `Re x ≥ 0`. -/
lemma norm_lin_ge (m : ℕ) {x : ℂ} (hx : 0 ≤ x.re) :
    (I3.nOf m : ℝ) ≤ ‖2 * (((I3.nOf m : ℝ) : ℂ) * x) + (I3.nOf m : ℂ) + 1‖ := by
  have h := Complex.abs_re_le_norm (2 * (((I3.nOf m : ℝ) : ℂ) * x) + (I3.nOf m : ℂ) + 1)
  have hre : (2 * (((I3.nOf m : ℝ) : ℂ) * x) + (I3.nOf m : ℂ) + 1).re
      = 2 * (I3.nOf m : ℝ) * x.re + I3.nOf m + 1 := by simp; ring
  rw [hre] at h
  have : (0 : ℝ) ≤ (I3.nOf m : ℝ) := Nat.cast_nonneg _
  have : 0 ≤ 2 * (I3.nOf m : ℝ) * x.re := by positivity
  have := le_abs_self (2 * (I3.nOf m : ℝ) * x.re + I3.nOf m + 1)
  linarith

/-- **(6.4.3)** `|μ(nx) - Ψ'(x)| ≤ (2 + 76 (4 + 1/(8 sin³(η/2)))/a)/n`. -/
theorem mu_asymp (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hx : SectorAt a η x) (hxre : 0 ≤ x.re) (hn : 4 / a ≤ (I3.nOf m : ℝ)) :
    ‖muI m ((I3.nOf m : ℝ) * x) - Psi1I x‖
      ≤ (2 + 76 * (4 + 1 / (8 * Real.sin (η / 2) ^ 3)) / a) / (I3.nOf m : ℝ) := by
  set n : ℝ := (I3.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hS := sectorHyp_of a η x hx
  have hd := norm_sum_digamma_sub_le univ cI (fun i => alphaI i x) βI sI hη0 hη ha hS hn
  rw [sum_abs_cs] at hd
  have hlog : ∑ i, (cI i : ℂ) * sI i * ((Real.log n : ℂ) + Complex.log (alphaI i x))
      = Psi1I x := by
    unfold Psi1I
    simp only [mul_add, sum_add_distrib]
    rw [← sum_mul, sum_cs_C, zero_mul, zero_add]
  rw [hlog] at hd
  have hlin := norm_lin_ge m hxre
  have hpos : 0 < ‖2 * ((n : ℂ) * x) + (I3.nOf m : ℂ) + 1‖ := lt_of_lt_of_le hnpos hlin
  have h1 : ‖(2 : ℂ) / (2 * ((n : ℂ) * x) + (I3.nOf m : ℂ) + 1)‖ ≤ 2 / n := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    exact div_le_div_of_nonneg_left (by norm_num) hnpos hlin
  have hmu : muI m ((n : ℂ) * x) - Psi1I x = 2 / (2 * ((n : ℂ) * x) + (I3.nOf m : ℂ) + 1)
      + (∑ i, (cI i : ℂ) * sI i * Complex.digamma ((n : ℂ) * alphaI i x + βI i) - Psi1I x) := by
    unfold muI
    rw [show ∑ i, (cI i : ℂ) * sI i * Complex.digamma (Gi m i ((n : ℂ) * x))
        = ∑ i, (cI i : ℂ) * sI i * Complex.digamma ((n : ℂ) * alphaI i x + βI i) from
      sum_congr rfl (fun i _ => by rw [Gi_scaled m i x n hn_def])]
    ring
  rw [hmu]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ 2 / n + 76 * ((4 + 1 / (8 * Real.sin (η / 2) ^ 3)) / (a * n)) := add_le_add h1 hd
    _ = _ := by field_simp

/-- **(6.4.3)** `|μ'(nx)| ≤ (4 + 76 (3 + 1/sin⁴(η/2))/a)/n` for `n ≥ 1`. -/
theorem mu1_bound (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hx : SectorAt a η x) (hxre : 0 ≤ x.re) (hn : 4 / a ≤ (I3.nOf m : ℝ))
    (hn1 : 1 ≤ (I3.nOf m : ℝ)) :
    ‖mu1I m ((I3.nOf m : ℝ) * x)‖
      ≤ (4 + 76 * (3 + 1 / Real.sin (η / 2) ^ 4) / a) / (I3.nOf m : ℝ) := by
  set n : ℝ := (I3.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := by linarith
  have hS := sectorHyp_of a η x hx
  have hd := norm_sum_deriv_digamma_le univ cI (fun i => alphaI i x) βI sI hη0 hη ha hS hn
  rw [sum_abs_cs2] at hd
  have hlin := norm_lin_ge m hxre
  have hpos : 0 < ‖2 * ((n : ℂ) * x) + (I3.nOf m : ℂ) + 1‖ := lt_of_lt_of_le hnpos hlin
  have h1 : ‖(-4 : ℂ) / (2 * ((n : ℂ) * x) + (I3.nOf m : ℂ) + 1) ^ 2‖ ≤ 4 / n := by
    rw [norm_div, norm_pow, show ‖(-4 : ℂ)‖ = 4 by simp]
    calc 4 / ‖2 * ((n : ℂ) * x) + (I3.nOf m : ℂ) + 1‖ ^ 2 ≤ 4 / n ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hnpos.le hlin 2)
      _ ≤ 4 / n := by
          apply div_le_div_of_nonneg_left (by norm_num) hnpos; nlinarith
  have hmu : mu1I m ((n : ℂ) * x) = -4 / (2 * ((n : ℂ) * x) + (I3.nOf m : ℂ) + 1) ^ 2
      + ∑ i, (cI i : ℂ) * sI i ^ 2 * deriv Complex.digamma ((n : ℂ) * alphaI i x + βI i) := by
    unfold mu1I
    rw [show ∑ i, (cI i : ℂ) * sI i ^ 2 * deriv Complex.digamma (Gi m i ((n : ℂ) * x))
        = ∑ i, (cI i : ℂ) * sI i ^ 2 * deriv Complex.digamma ((n : ℂ) * alphaI i x + βI i) from
      sum_congr rfl (fun i _ => by rw [Gi_scaled m i x n hn_def])]
  rw [hmu]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ 4 / n + 76 * ((3 + 1 / Real.sin (η / 2) ^ 4) / (a * n)) := add_le_add h1 hd
    _ = _ := by field_simp

/-- **The `q`-identity** for `H_n`. -/
theorem q_mul_Hn (m : ℕ) (z : ℂ) :
    Complex.exp (2 * π * I * z) * Hn m z =
      ((-1 + 2 * Complex.exp (2 * π * I * z) - Complex.exp (2 * π * I * z) ^ 2) *
          (muI m z ^ 2 + mu1I m z)
        + 6 * π * I * muI m z * (1 - Complex.exp (2 * π * I * z) ^ 2)
        + 3 * π ^ 2 * (3 + 2 * Complex.exp (2 * π * I * z)
          + 3 * Complex.exp (2 * π * I * z) ^ 2)) / 4 := by
  set A := Complex.exp (π * z * I) with hA
  have hA0 : A ≠ 0 := Complex.exp_ne_zero _
  have hinv : Complex.exp (-(π * z) * I) = A⁻¹ := by
    rw [hA, ← Complex.exp_neg]; ring_nf
  have hq : Complex.exp (2 * π * I * z) = A ^ 2 := by
    rw [hA, ← Complex.exp_nat_mul]; ring_nf
  have hs : Complex.sin (π * z) = (A⁻¹ - A) * I / 2 := by
    rw [Complex.sin, hinv]
  have hc : Complex.cos (π * z) = (A + A⁻¹) / 2 := by
    rw [Complex.cos, hinv]
  unfold Hn
  rw [hs, hc, hq]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end BetaIrr.I3.Analytic
