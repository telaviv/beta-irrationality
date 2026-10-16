/-
# The integrand on the contour: `F_n(nx) = e^{λ_n + n f(x)} · n · A_n(x)`

For `Im x > 0`, `Re x ≥ 0`, the sector condition at `x`, and `n ≥ max(4/a, 1)`:

    F_n(nx) = e^{λ_n + n f(x)} · n · A_n(x),
    A_n(x) = (2x + 1 + 1/n) e^{ψ₀(x) + e} Q / π²,   Q = e^{2πinx} H_n(nx),       (`Fn_path`)

with `|e| ≤ c_e/n`, `|μ(nx) - Ψ'(x)| ≤ c_μ/n`, `|μ'(nx)| ≤ c_μ'/n` (`PathAsymp.lean`) and `Q` given by
the `q`-identity. The abstract bounds `amp_bound` (for (U)) and `amp_diff_bound` (for (M)) then give

    |A_n(x)| ≤ 420 B⁴ / π²,     |A_n(x) - A(x)| ≤ 600 B⁴ δ / π²,
    A(x) = (2x + 1) e^{ψ₀(x)} (-(Ψ'(x) - 3πi)²/4) / π²,

for any `B ≥ 1` dominating `|2x+1|`, `|e^{ψ₀(x)}|`, `|Ψ'(x)|`, and `δ ≤ 1` dominating the small
quantities. `growth_*` give such `B` from `‖x‖` alone.

Mirrors `Analytic/FnPath.lean` (instance I3: `Σ|c_i| = 76`, `Σ|c_i(β_i - 1/2)| = 41`); `Qform`
and its bounds are in `Fam/Analytic/Helpers.lean`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.PathAsymp
import BetaIrrational.Analytic.Laplace

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real Finset Filter Topology
open BetaIrr.Analytic BetaIrr.Fam.Analytic


/-- Constants of `PathAsymp`. -/
noncomputable def cE (a η : ℝ) : ℝ := 76 * ((9 + 1 / (6 * Real.sin (η / 2) ^ 2)) / a)
noncomputable def cMu (a η : ℝ) : ℝ := 2 + 76 * (4 + 1 / (8 * Real.sin (η / 2) ^ 3)) / a
noncomputable def cMu1 (a η : ℝ) : ℝ := 4 + 76 * (3 + 1 / Real.sin (η / 2) ^ 4) / a

/-- **The integrand on the contour.** -/
theorem Fn_path (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hxim : 0 < x.im) (hx : SectorAt a η x) (hn : 4 / a ≤ (I3.nOf m : ℝ)) :
    ∃ e : ℂ, ‖e‖ ≤ cE a η / (I3.nOf m : ℝ) ∧
      Fn m ((I3.nOf m : ℝ) * x) =
        Complex.exp (lamN (I3.nOf m) + (I3.nOf m : ℝ) * phaseI x) * ((I3.nOf m : ℝ) : ℂ) *
          ((2 * x + 1 + 1 / (I3.nOf m : ℝ)) * Complex.exp (psi0I x + e) *
            Qform (muI m ((I3.nOf m : ℝ) * x)) (mu1I m ((I3.nOf m : ℝ) * x))
              (Complex.exp (2 * π * I * ((I3.nOf m : ℝ) * x))) / π ^ 2) := by
  set n : ℝ := (I3.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  obtain ⟨e, he, hP⟩ := Pfun_asymp m ha hη0 hη hx hn
  refine ⟨e, ?_, ?_⟩
  · refine he.trans (le_of_eq ?_)
    unfold cE; rw [← hn_def]; field_simp
  have hzim : 0 < ((n : ℂ) * x).im := by simp; positivity
  rw [Fn_eq_PH m hzim, hP]
  have hq := q_mul_Hn m ((n : ℂ) * x)
  have hqne : Complex.exp (2 * π * I * ((n : ℂ) * x)) ≠ 0 := Complex.exp_ne_zero _
  have hH : Hn m ((n : ℂ) * x) = Complex.exp (-(2 * π * I * ((n : ℂ) * x))) *
      Qform (muI m ((n : ℂ) * x)) (mu1I m ((n : ℂ) * x))
        (Complex.exp (2 * π * I * ((n : ℂ) * x))) := by
    unfold Qform
    rw [← hq, ← mul_assoc, ← Complex.exp_add]
    simp
  rw [hH]
  have hexp : Complex.exp (lamN n + n * PsiI x + psi0I x + e) *
      Complex.exp (-(2 * π * I * ((n : ℂ) * x)))
      = Complex.exp (lamN n + n * phaseI x) * Complex.exp (psi0I x + e) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold phaseI; ring
  have := hπC
  calc (n : ℂ) * (2 * x + 1 + 1 / n) * Complex.exp (lamN n + n * PsiI x + psi0I x + e) *
        (Complex.exp (-(2 * π * I * ((n : ℂ) * x))) * Qform (muI m ((n : ℂ) * x))
          (mu1I m ((n : ℂ) * x)) (Complex.exp (2 * π * I * ((n : ℂ) * x)))) / π ^ 2
      = (Complex.exp (lamN n + n * PsiI x + psi0I x + e) *
          Complex.exp (-(2 * π * I * ((n : ℂ) * x)))) * (n : ℂ) * ((2 * x + 1 + 1 / n) *
          Qform (muI m ((n : ℂ) * x)) (mu1I m ((n : ℂ) * x))
            (Complex.exp (2 * π * I * ((n : ℂ) * x))) / π ^ 2) := by ring
    _ = _ := by rw [hexp]; ring

/-! ### Abstract amplitude bounds -/

/-- The amplitude `A_n` as a function of the data. -/
noncomputable def Amp (x e μ μ1 q h : ℂ) : ℂ :=
  (2 * x + 1 + h) * Complex.exp (psi0I x + e) * Qform μ μ1 q / π ^ 2

/-- The limiting amplitude `A(x) = (2x+1) e^{ψ₀(x)} (-(Ψ'(x) - 3πi)²/4) / π²`. -/
noncomputable def Alim (x : ℂ) : ℂ :=
  (2 * x + 1) * Complex.exp (psi0I x) * (-(Psi1I x - 3 * π * I) ^ 2 / 4) / π ^ 2

/-- **(U)-type bound** for the amplitude. -/
theorem amp_bound {x e μ μ1 q h : ℂ} {B : ℝ} (hB : 1 ≤ B) (hX : ‖2 * x + 1‖ ≤ B)
    (hE : ‖Complex.exp (psi0I x)‖ ≤ B) (hμ : ‖μ‖ ≤ 2 * B) (hμ1 : ‖μ1‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (he : ‖e‖ ≤ 1) (hh : ‖h‖ ≤ 1) : ‖Amp x e μ μ1 q h‖ ≤ 600 * B ^ 4 / π ^ 2 := by
  unfold Amp
  rw [norm_div, norm_pi_sq, norm_mul, norm_mul, Complex.exp_add, norm_mul]
  apply div_le_div_of_nonneg_right _ hπ2.le
  have h1 : ‖2 * x + 1 + h‖ ≤ 2 * B := by
    calc ‖2 * x + 1 + h‖ ≤ ‖2 * x + 1‖ + ‖h‖ := norm_add_le _ _
      _ ≤ 2 * B := by linarith
  have h2 := norm_exp_le_three he
  have h3 := norm_Qform_le hB hμ hμ1 hq
  calc ‖2 * x + 1 + h‖ * (‖Complex.exp (psi0I x)‖ * ‖Complex.exp e‖) * ‖Qform μ μ1 q‖
      ≤ (2 * B) * (B * 3) * (100 * B ^ 2) := by gcongr
    _ = 600 * B ^ 4 := by ring

/-- **(M)-type bound**: `|A_n - A| ≤ 700 B⁴ δ / π²`. -/
theorem amp_diff_bound {x e μ μ1 q h : ℂ} {B δ : ℝ} (hB : 1 ≤ B) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hX : ‖2 * x + 1‖ ≤ B) (hE : ‖Complex.exp (psi0I x)‖ ≤ B) (hP : ‖Psi1I x‖ ≤ B)
    (he : ‖e‖ ≤ δ) (hν : ‖μ - Psi1I x‖ ≤ δ) (hμ1 : ‖μ1‖ ≤ δ) (hq : ‖q‖ ≤ δ) (hh : ‖h‖ ≤ δ) :
    ‖Amp x e μ μ1 q h - Alim x‖ ≤ 700 * B ^ 4 * δ / π ^ 2 := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  set P := Psi1I x
  set E := Complex.exp (psi0I x)
  set X := 2 * x + 1
  have hμ : ‖μ‖ ≤ 2 * B := by
    calc ‖μ‖ = ‖(μ - P) + P‖ := by ring_nf
      _ ≤ ‖μ - P‖ + ‖P‖ := norm_add_le _ _
      _ ≤ 2 * B := by linarith
  have hQ := norm_Qform_le hB hμ (hμ1.trans hδ) (hq.trans hδ)
  have hR : ‖(2 - q) * (μ ^ 2 + μ1) - 6 * π * I * μ * q + 3 * π ^ 2 * (2 + 3 * q)‖
      ≤ 202 * B ^ 2 := by
    have hq1 : ‖q‖ ≤ 1 := hq.trans hδ
    have a1 : ‖(2 : ℂ) - q‖ ≤ 3 := by
      calc ‖(2 : ℂ) - q‖ ≤ ‖(2 : ℂ)‖ + ‖q‖ := norm_sub_le _ _
        _ ≤ 3 := by simp; linarith
    have a2 : ‖μ ^ 2 + μ1‖ ≤ 4 * B ^ 2 + 1 := by
      calc ‖μ ^ 2 + μ1‖ ≤ ‖μ‖ ^ 2 + ‖μ1‖ := by rw [← norm_pow]; exact norm_add_le _ _
        _ ≤ (2 * B) ^ 2 + 1 := by gcongr; exact hμ1.trans hδ
        _ = 4 * B ^ 2 + 1 := by ring
    have a3 : ‖6 * (π : ℂ) * I * μ * q‖ ≤ 6 * π * (2 * B) := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hπ0, show ‖(6 : ℂ)‖ = 6 by simp]
      calc 6 * π * 1 * ‖μ‖ * ‖q‖ ≤ 6 * π * 1 * (2 * B) * 1 := by gcongr
        _ = 6 * π * (2 * B) := by ring
    have a4 : ‖3 * (π : ℂ) ^ 2 * (2 + 3 * q)‖ ≤ 3 * π ^ 2 * 5 := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ0,
        show ‖(3 : ℂ)‖ = 3 by simp]
      have : ‖(2 : ℂ) + 3 * q‖ ≤ 5 := by
        calc ‖(2 : ℂ) + 3 * q‖ ≤ ‖(2 : ℂ)‖ + ‖(3 : ℂ) * q‖ := norm_add_le _ _
          _ ≤ 5 := by simp [norm_mul]; linarith
      gcongr
    calc _ ≤ ‖(2 - q) * (μ ^ 2 + μ1)‖ + ‖6 * (π : ℂ) * I * μ * q‖
          + ‖3 * (π : ℂ) ^ 2 * (2 + 3 * q)‖ := norm_add_le_of_le (norm_sub_le _ _) le_rfl
      _ ≤ 3 * (4 * B ^ 2 + 1) + 6 * π * (2 * B) + 3 * π ^ 2 * 5 := by
          rw [norm_mul]
          gcongr
      _ ≤ 202 * B ^ 2 := by nlinarith
  have hQQ : ‖Qform μ μ1 q - (-(P - 3 * π * I) ^ 2 / 4)‖ ≤ 57 * B ^ 2 * δ := by
    rw [Qform_sub]
    have b1 : ‖-(μ - P) * (μ + P - 6 * π * I) / 4‖ ≤ δ * (22 * B) / 4 := by
      rw [norm_div, norm_mul, norm_neg, show ‖(4 : ℂ)‖ = 4 by simp]
      have : ‖μ + P - 6 * π * I‖ ≤ 22 * B := by
        calc ‖μ + P - 6 * π * I‖ ≤ ‖μ‖ + ‖P‖ + ‖(6 * π * I : ℂ)‖ :=
              norm_sub_le_of_le (norm_add_le _ _) le_rfl
          _ ≤ 2 * B + B + 6 * π := by
              gcongr
              rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos hπ0]
              simp
          _ ≤ 22 * B := by nlinarith
      gcongr
    have b2 : ‖μ1 / 4‖ ≤ δ / 4 := by
      rw [norm_div, show ‖(4 : ℂ)‖ = 4 by simp]; gcongr
    have b3 : ‖q * ((2 - q) * (μ ^ 2 + μ1) - 6 * π * I * μ * q + 3 * π ^ 2 * (2 + 3 * q)) / 4‖
        ≤ δ * (202 * B ^ 2) / 4 := by
      rw [norm_div, norm_mul, show ‖(4 : ℂ)‖ = 4 by simp]; gcongr
    calc _ ≤ ‖-(μ - P) * (μ + P - 6 * π * I) / 4‖ + ‖μ1 / 4‖ + ‖q * ((2 - q) * (μ ^ 2 + μ1)
          - 6 * π * I * μ * q + 3 * π ^ 2 * (2 + 3 * q)) / 4‖ :=
          norm_add_le_of_le (norm_sub_le _ _) le_rfl
      _ ≤ δ * (22 * B) / 4 + δ / 4 + δ * (202 * B ^ 2) / 4 := add_le_add_three b1 b2 b3
      _ ≤ 57 * B ^ 2 * δ := by
          have h' : 0 ≤ 26 * B ^ 2 - 22 * B - 1 := by nlinarith
          nlinarith [mul_nonneg hδ0 h']
  have he1 : ‖e‖ ≤ 1 := he.trans hδ
  have hexp3 := norm_exp_le_three he1
  have hexp1 : ‖Complex.exp e - 1‖ ≤ 3 * δ := by
    calc ‖Complex.exp e - 1‖ ≤ ‖e‖ * Real.exp ‖e‖ := norm_cexp_sub_one_le_mul_exp e
      _ ≤ δ * 3 := by
          gcongr
          calc Real.exp ‖e‖ ≤ Real.exp 1 := Real.exp_le_exp.2 he1
            _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
      _ = 3 * δ := by ring
  have hsplit : Amp x e μ μ1 q h - Alim x =
      (h * E * Complex.exp e * Qform μ μ1 q + X * E * (Complex.exp e - 1) * Qform μ μ1 q
        + X * E * (Qform μ μ1 q - (-(P - 3 * π * I) ^ 2 / 4))) / π ^ 2 := by
    unfold Amp Alim
    rw [Complex.exp_add]
    ring
  rw [hsplit, norm_div, norm_pi_sq]
  apply div_le_div_of_nonneg_right _ hπ2.le
  calc _ ≤ ‖h * E * Complex.exp e * Qform μ μ1 q‖ + ‖X * E * (Complex.exp e - 1) * Qform μ μ1 q‖
        + ‖X * E * (Qform μ μ1 q - (-(P - 3 * π * I) ^ 2 / 4))‖ := norm_add₃_le
    _ ≤ δ * B * 3 * (100 * B ^ 2) + B * B * (3 * δ) * (100 * B ^ 2)
        + B * B * (57 * B ^ 2 * δ) := by
        simp only [norm_mul]
        gcongr
    _ ≤ 700 * B ^ 4 * δ := by
        have : B ^ 3 ≤ B ^ 4 := pow_le_pow_right₀ hB (by norm_num)
        have h2 := mul_le_mul_of_nonneg_right this hδ0
        have hY : 0 ≤ B ^ 4 * δ := by positivity
        have e : δ * B * 3 * (100 * B ^ 2) + B * B * (3 * δ) * (100 * B ^ 2)
            + B * B * (57 * B ^ 2 * δ) = 300 * (B ^ 3 * δ) + 357 * (B ^ 4 * δ) := by ring
        rw [e]; linarith

/-! ### Growth of `Ψ'`, `ψ₀` -/

lemma norm_alphaI_le (i : Fin 58) (x : ℂ) : ‖alphaI i x‖ ≤ ‖x‖ + 3 := by
  unfold alphaI
  have hs : ‖(sI i : ℂ)‖ = 1 := by
    have := sI_sq i
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg (sI i), sq_abs (sI i)]
  have hu : ‖(uI i : ℂ)‖ ≤ 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact uI_bound i
  calc ‖(sI i : ℂ) * x + uI i‖ ≤ ‖(sI i : ℂ) * x‖ + ‖(uI i : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖x‖ + 3 := by rw [norm_mul, hs, one_mul]; linarith

/-- `ℓ(r) = r + 3 + |log a| + π`. -/
noncomputable def ellA (a : ℝ) (r : ℝ) : ℝ := r + 3 + |Real.log a| + π

lemma norm_log_alphaI_le {a : ℝ} (ha : 0 < a) {x : ℂ} (i : Fin 58) (hx : a ≤ ‖alphaI i x‖) :
    ‖Complex.log (alphaI i x)‖ ≤ ellA a ‖x‖ := by
  unfold ellA
  have := norm_log_le_of_ge ha hx
  have := norm_alphaI_le i x
  linarith

lemma norm_cs_eq (i : Fin 58) : ‖(cI i : ℂ) * (sI i : ℂ)‖ = |(cI i : ℝ) * sI i| := by
  rw [show ((cI i : ℤ) : ℂ) * (sI i : ℂ) = ((((cI i : ℤ) : ℝ) * sI i : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]

lemma norm_cβ_eq (i : Fin 58) :
    ‖(cI i : ℂ) * ((βI i : ℂ) - 1 / 2)‖ = |(cI i : ℝ) * (βI i - 1 / 2)| := by
  rw [show ((cI i : ℤ) : ℂ) * ((βI i : ℂ) - 1 / 2)
      = ((((cI i : ℤ) : ℝ) * (βI i - 1 / 2) : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]

lemma norm_Psi1I_le {a : ℝ} (ha : 0 < a) {x : ℂ} (hx : ∀ i, a ≤ ‖alphaI i x‖) :
    ‖Psi1I x‖ ≤ 76 * ellA a ‖x‖ := by
  unfold Psi1I
  refine (norm_sum_le _ _).trans ?_
  rw [← sum_abs_cs, sum_mul]
  refine sum_le_sum (fun i _ => ?_)
  rw [norm_mul, norm_cs_eq]
  exact mul_le_mul_of_nonneg_left (norm_log_alphaI_le ha i (hx i)) (abs_nonneg _)

lemma norm_psi0I_le {a : ℝ} (ha : 0 < a) {x : ℂ} (hx : ∀ i, a ≤ ‖alphaI i x‖) :
    ‖psi0I x‖ ≤ 41 * ellA a ‖x‖ := by
  unfold psi0I
  refine (norm_sum_le _ _).trans ?_
  rw [← sum_abs_cβ, sum_mul]
  refine sum_le_sum (fun i _ => ?_)
  rw [norm_mul, norm_cβ_eq]
  exact mul_le_mul_of_nonneg_left (norm_log_alphaI_le ha i (hx i)) (abs_nonneg _)

/-- A single bound `B(r) ≥ 1` dominating `‖2x+1‖`, `‖e^{ψ₀(x)}‖`, `‖Ψ'(x)‖` for `‖x‖ ≤ r`. -/
noncomputable def Bgrowth (a r : ℝ) : ℝ := Real.exp (41 * ellA a r) + 76 * ellA a r + 2 * r + 1

lemma ellA_pos (a : ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 < ellA a r := by
  unfold ellA; have := Real.pi_pos; positivity

lemma one_le_Bgrowth (a : ℝ) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ Bgrowth a r := by
  unfold Bgrowth
  have := ellA_pos a hr
  have := Real.exp_pos (41 * ellA a r)
  linarith

lemma Bgrowth_mono (a : ℝ) {r s : ℝ} (hrs : r ≤ s) : Bgrowth a r ≤ Bgrowth a s := by
  unfold Bgrowth ellA
  gcongr

theorem growth_bounds {a : ℝ} (ha : 0 < a) {x : ℂ} (hx : ∀ i, a ≤ ‖alphaI i x‖) {r : ℝ}
    (hr : ‖x‖ ≤ r) :
    ‖2 * x + 1‖ ≤ Bgrowth a r ∧ ‖Complex.exp (psi0I x)‖ ≤ Bgrowth a r ∧
      ‖Psi1I x‖ ≤ Bgrowth a r := by
  have hmono := Bgrowth_mono a hr
  have hℓ := ellA_pos a (norm_nonneg x)
  have hex := Real.exp_pos (41 * ellA a ‖x‖)
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ hmono
    calc ‖2 * x + 1‖ ≤ ‖2 * x‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 * ‖x‖ + 1 := by simp [norm_mul]
      _ ≤ Bgrowth a ‖x‖ := by unfold Bgrowth; nlinarith
  · refine le_trans ?_ hmono
    rw [Complex.norm_exp]
    calc Real.exp (psi0I x).re ≤ Real.exp (41 * ellA a ‖x‖) := by
          gcongr
          exact (Complex.re_le_norm _).trans (norm_psi0I_le ha hx)
      _ ≤ Bgrowth a ‖x‖ := by unfold Bgrowth; nlinarith [norm_nonneg x]
  · refine le_trans ?_ hmono
    refine (norm_Psi1I_le ha hx).trans ?_
    unfold Bgrowth; nlinarith [norm_nonneg x]

end BetaIrr.I3.Analytic
