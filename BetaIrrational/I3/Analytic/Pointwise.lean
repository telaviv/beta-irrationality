/-
# Pointwise integrand bounds (U) and (M) for instance I3

Mirrors the second half of `Analytic/SaddleData.lean` (the structure itself is in
`I3/Analytic/SaddleData.lean`). No certificate is needed:
* `norm_Fn_le` (the bound (U)): `|F_n(nx)| ≤ e^{λ_n + n Re f(x)} n · 600 B⁴/π²`;
* `Fn_disc_approx` (the form (M)):
  `|F_n(nx) e^{-λ_n - nΩ}/n - e^{n(f(x) - Ω)} A(x)| ≤ |e^{n(f(x)-Ω)}| · 700 B⁴ δ_n/π²`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.PhaseDeriv
import BetaIrrational.I3.Analytic.SaddleData

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real Finset Filter Topology Set
open BetaIrr.Analytic BetaIrr.Fam.Analytic

/-! ### Pointwise bounds -/

/-- The "large `n`" conditions used below. -/
def LargeN (a η n : ℝ) : Prop :=
  4 / a ≤ n ∧ 1 ≤ n ∧ cE a η ≤ n ∧ cMu a η ≤ n ∧ cMu1 a η ≤ n

lemma norm_exp_lam (n : ℝ) (w : ℂ) :
    ‖Complex.exp (lamN n + (n : ℂ) * w)‖ = Real.exp (lamN n + n * w.re) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- **(U)**: `|F_n(nx)| ≤ e^{λ_n + n Re f(x)} n · 600 B⁴/π²`. -/
theorem norm_Fn_le (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hxim : 0 < x.im) (hxre : 0 ≤ x.re) (hx : SectorAt a η x) {R : ℝ} (hR : ‖x‖ ≤ R)
    (hn : LargeN a η (I3.nOf m : ℝ)) :
    ‖Fn m ((I3.nOf m : ℝ) * x)‖ ≤ Real.exp (lamN (I3.nOf m) + (I3.nOf m : ℝ) * (phaseI x).re)
      * (I3.nOf m : ℝ) * (600 * Bgrowth a R ^ 4 / π ^ 2) := by
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := hn
  set n : ℝ := (I3.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := by linarith
  obtain ⟨e, he, hF⟩ := Fn_path m ha hη0 hη hxim hx hn1
  rw [← hn_def] at hF he
  rw [hF]
  have hxsec : ∀ i, a ≤ ‖alphaI i x‖ := fun i => (hx i).1
  obtain ⟨gX, gE, gP⟩ := growth_bounds ha hxsec hR
  set B := Bgrowth a R
  have hB : 1 ≤ B := one_le_Bgrowth a ((norm_nonneg x).trans hR)
  have hmu := mu_asymp m ha hη0 hη hx hxre hn1
  have hmu1 := mu1_bound m ha hη0 hη hx hxre hn1 hn2
  rw [← hn_def] at hmu hmu1
  have hμ : ‖muI m ((n : ℂ) * x)‖ ≤ 2 * B := by
    have : ‖muI m ((n : ℂ) * x)‖ ≤ ‖Psi1I x‖ + cMu a η / n := by
      have h := norm_sub_norm_le (muI m ((n : ℂ) * x)) (Psi1I x)
      unfold cMu; linarith
    have : cMu a η / n ≤ 1 := by rw [div_le_one hnpos]; exact hn4
    linarith
  have hμ1 : ‖mu1I m ((n : ℂ) * x)‖ ≤ 1 :=
    hmu1.trans (by rw [div_le_one hnpos]; unfold cMu1 at hn5; exact hn5)
  have hq : ‖Complex.exp (2 * π * I * ((n : ℂ) * x))‖ ≤ 1 := by
    rw [norm_exp_two_pi_I_mul]
    apply Real.exp_le_one_iff.2
    have := Real.pi_pos
    have : 0 ≤ 2 * π * n * x.im := by positivity
    linarith
  have he1 : ‖e‖ ≤ 1 := he.trans (by rw [div_le_one hnpos]; exact hn3)
  have hh : ‖((1 / n : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_le_one hnpos]; exact hn2
  have hA := amp_bound (x := x) (e := e) (μ := muI m ((n : ℂ) * x))
    (μ1 := mu1I m ((n : ℂ) * x)) (q := Complex.exp (2 * π * I * ((n : ℂ) * x)))
    (h := ((1 / n : ℝ) : ℂ)) hB gX gE hμ hμ1 hq he1 hh
  rw [norm_mul, norm_mul, norm_exp_lam, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
  gcongr
  unfold Amp at hA
  push_cast at hA
  exact hA

/-- The small quantity `δ_n` on the disc. -/
noncomputable def deltaN (a η n y₁ : ℝ) : ℝ :=
  (cE a η + cMu a η + cMu1 a η + 1) / n + Real.exp (-(2 * π * n * y₁))

lemma cE_pos {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) : 0 < cE a η := by
  unfold cE
  have : 0 < Real.sin (η / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  positivity

lemma cMu_pos {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) : 0 < cMu a η := by
  unfold cMu
  have : 0 < Real.sin (η / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  positivity

lemma cMu1_pos {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) : 0 < cMu1 a η := by
  unfold cMu1
  have : 0 < Real.sin (η / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  positivity

/-- **(M)**: on the disc, `F_n(nx) e^{-λ_n - nΩ}/n ≈ e^{n(f(x) - Ω)} A(x)`. -/
theorem Fn_disc_approx (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hxim : 0 < x.im) (hxre : 0 ≤ x.re) (hx : SectorAt a η x) {R y₁ : ℝ} (hR : ‖x‖ ≤ R)
    (hy₁ : y₁ ≤ x.im) (Ω : ℂ) (hn : LargeN a η (I3.nOf m : ℝ))
    (hδ : deltaN a η (I3.nOf m : ℝ) y₁ ≤ 1) :
    ‖Fn m ((I3.nOf m : ℝ) * x) * Complex.exp (-(lamN (I3.nOf m) + (I3.nOf m : ℝ) * Ω))
        / (I3.nOf m : ℝ) - Complex.exp ((I3.nOf m : ℝ) * (phaseI x - Ω)) * Alim x‖
      ≤ ‖Complex.exp ((I3.nOf m : ℝ) * (phaseI x - Ω))‖ *
        (700 * Bgrowth a R ^ 4 * deltaN a η (I3.nOf m : ℝ) y₁ / π ^ 2) := by
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := hn
  set n : ℝ := (I3.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := by linarith
  obtain ⟨e, he, hF⟩ := Fn_path m ha hη0 hη hxim hx hn1
  rw [← hn_def] at hF he
  have hxsec : ∀ i, a ≤ ‖alphaI i x‖ := fun i => (hx i).1
  obtain ⟨gX, gE, gP⟩ := growth_bounds ha hxsec hR
  set B := Bgrowth a R
  have hB : 1 ≤ B := one_le_Bgrowth a ((norm_nonneg x).trans hR)
  have hmu := mu_asymp m ha hη0 hη hx hxre hn1
  have hmu1 := mu1_bound m ha hη0 hη hx hxre hn1 hn2
  rw [← hn_def] at hmu hmu1
  set δ := deltaN a η n y₁ with hδdef
  have hcE := cE_pos ha hη0 hη
  have hcM := cMu_pos ha hη0 hη
  have hcM1 := cMu1_pos ha hη0 hη
  have hδ0 : 0 ≤ δ := by rw [hδdef]; unfold deltaN; positivity
  have hsmall : ∀ c : ℝ, 0 ≤ c → c ≤ cE a η + cMu a η + cMu1 a η + 1 → c / n ≤ δ := by
    intro c hc hc'
    rw [hδdef]; unfold deltaN
    have : c / n ≤ (cE a η + cMu a η + cMu1 a η + 1) / n := by gcongr
    have := Real.exp_pos (-(2 * π * n * y₁))
    linarith
  have he' : ‖e‖ ≤ δ := he.trans (hsmall _ hcE.le (by linarith))
  have hν : ‖muI m ((n : ℂ) * x) - Psi1I x‖ ≤ δ :=
    hmu.trans (by
      have := hsmall (cMu a η) hcM.le (by linarith)
      unfold cMu at this; exact this)
  have hμ1 : ‖mu1I m ((n : ℂ) * x)‖ ≤ δ :=
    hmu1.trans (by
      have := hsmall (cMu1 a η) hcM1.le (by linarith)
      unfold cMu1 at this; exact this)
  have hq : ‖Complex.exp (2 * π * I * ((n : ℂ) * x))‖ ≤ δ := by
    rw [norm_exp_two_pi_I_mul, hδdef]; unfold deltaN
    have h1 : Real.exp (-(2 * π * n * x.im)) ≤ Real.exp (-(2 * π * n * y₁)) := by
      gcongr
    have : 0 ≤ (cE a η + cMu a η + cMu1 a η + 1) / n := by positivity
    linarith
  have hh : ‖((1 / n : ℝ) : ℂ)‖ ≤ δ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact hsmall 1 zero_le_one (by linarith)
  have hA := amp_diff_bound (x := x) (e := e) (μ := muI m ((n : ℂ) * x))
    (μ1 := mu1I m ((n : ℂ) * x)) (q := Complex.exp (2 * π * I * ((n : ℂ) * x)))
    (h := ((1 / n : ℝ) : ℂ)) hB hδ0 hδ gX gE gP he' hν hμ1 hq hh
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hrewrite : Fn m ((n : ℂ) * x) * Complex.exp (-(lamN n + (n : ℂ) * Ω)) / n
      = Complex.exp ((n : ℂ) * (phaseI x - Ω)) * Amp x e (muI m ((n : ℂ) * x))
          (mu1I m ((n : ℂ) * x)) (Complex.exp (2 * π * I * ((n : ℂ) * x))) ((1 / n : ℝ) : ℂ) := by
    rw [hF]
    unfold Amp
    have hexp : Complex.exp (lamN n + (n : ℂ) * phaseI x) * Complex.exp (-(lamN n + (n : ℂ) * Ω))
        = Complex.exp ((n : ℂ) * (phaseI x - Ω)) := by
      rw [← Complex.exp_add]; congr 1; ring
    push_cast
    field_simp
    rw [← hexp]
    ring
  rw [hrewrite, ← mul_sub, norm_mul]
  gcongr

end BetaIrr.I3.Analytic
