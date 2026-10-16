/-
# The saddle value `Ω = f(x₀)` and (H4) for instance I3 (PROOF_BETA §6.3, §7 (H3), (H4))

With `x₀` the certified saddle of `SaddleI3.lean` and `Ω = f(x₀) = Ψ(x₀) - 2πi x₀`:
* `I3_ReOmega_le : Re Ω ≤ -29.7790172`, `I3_ReOmega_ge : -29.7790173 ≤ Re Ω` — (S0)/(H3);
* `I3_ImOmega_mem : Im Ω ∈ [-7.301075589, -7.301075587]`;
* `I3_sinqtheta_ge : 99/100 < sin(480 Im Ω)` — (H4) (`sin(480 Im Ω) ≈ 0.99757`).

Method: a box evaluation of `f(c0)` at the rational centre (precision `2^{-80}`, 40 series terms),
widened by the mean-value bound `‖f(x₀) - f(c0)‖ ≤ (10⁻¹⁶ + 300 R0) R0`. For (H4),
`480 Im Ω = (u + π/2) - 558 · 2π` with `|u| ≤ 0.07` (kernel check), so
`sin(480 Im Ω) = cos u ≥ 1 - u²/2`.

All numerical checks are `decide +kernel` (no `native_decide`).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Interval.SaddleI3
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace BetaIrr.I3.Interval

open Complex Metric BetaIrr.Interval BetaIrr.Interval.IV Real

/-- **`Ω = f(x₀)`**, the saddle value. -/
noncomputable def Ω : ℂ := f x₀

def fP : CB := (psiB pp nn facI3 P0).sub (twoPiI.mul P0)

lemma mem_fP : fP.mem (f c0) :=
  CB.mem_sub (mem_psiB pp nn facI3 mem_P0) (CB.mem_mul mem_twoPiI mem_P0)

/-- The radius by which `f c0`'s box is widened. -/
def wΩ : ℚ := (1 / 10 ^ 16 + 300 * R0) * R0

lemma norm_Ω_sub : ‖Ω - f c0‖ ≤ (wΩ : ℝ) := by
  have hmv := (convex_closedBall c0 (R0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := g) (C := ((1 / 10 ^ 16 + 300 * R0 : ℚ) : ℝ))
    (fun w hw => (I3_hasDerivAt_f (im_ne_of_ball hw)).hasDerivWithinAt)
    (fun w hw => norm_g_le hw) c0_mem saddle_mem
  have hzc : ‖x₀ - c0‖ ≤ R0 := by rw [← dist_eq_norm]; exact saddle_mem
  have hC : (0 : ℝ) ≤ ((1 / 10 ^ 16 + 300 * R0 : ℚ) : ℝ) := by norm_num [R0]
  calc ‖Ω - f c0‖ ≤ ((1 / 10 ^ 16 + 300 * R0 : ℚ) : ℝ) * ‖x₀ - c0‖ := hmv
    _ ≤ ((1 / 10 ^ 16 + 300 * R0 : ℚ) : ℝ) * R0 := mul_le_mul_of_nonneg_left hzc hC
    _ = (wΩ : ℝ) := by simp [wΩ]

/-- Interval for `Re Ω`. -/
def ReΩI : IV := fP.re.widen wΩ
/-- Interval for `Im Ω`. -/
def ImΩI : IV := fP.im.widen wΩ

lemma mem_ReΩI : ReΩI.mem Ω.re := by
  refine mem_widen mem_fP.1 ?_
  rw [← sub_re]; exact (abs_re_le_norm _).trans norm_Ω_sub

lemma mem_ImΩI : ImΩI.mem Ω.im := by
  refine mem_widen mem_fP.2 ?_
  rw [← sub_im]; exact (abs_im_le_norm _).trans norm_Ω_sub

lemma chk_Re_hi : ReΩI.hiLe (-297790172 / 10 ^ 7) = true := by decide +kernel
lemma chk_Re_lo : ReΩI.loGe (-297790173 / 10 ^ 7) = true := by decide +kernel
lemma chk_Im_hi : ImΩI.hiLe (-7301075587 / 10 ^ 9) = true := by decide +kernel
lemma chk_Im_lo : ImΩI.loGe (-7301075589 / 10 ^ 9) = true := by decide +kernel

/-- **(H3)/(S0)**: `Re Ω ≤ -29.7790172`. -/
theorem I3_ReOmega_le : Ω.re ≤ -297790172 / 10 ^ 7 := by
  have := le_of_hiLe mem_ReΩI chk_Re_hi
  push_cast at this; exact this

theorem I3_ReOmega_ge : -297790173 / 10 ^ 7 ≤ Ω.re := by
  have := ge_of_loGe mem_ReΩI chk_Re_lo
  push_cast at this; exact this

theorem I3_ImOmega_mem : -7301075589 / 10 ^ 9 ≤ Ω.im ∧ Ω.im ≤ -7301075587 / 10 ^ 9 := by
  have h1 := ge_of_loGe mem_ImΩI chk_Im_lo
  have h2 := le_of_hiLe mem_ImΩI chk_Im_hi
  push_cast at h1 h2; exact ⟨h1, h2⟩

/-! ## (H4): `sin(480 Im Ω) > 0.99` -/

/-- `u = 480 Im Ω + (2231/2) π`, so that `480 Im Ω = (u + π/2) - 558 · 2π`. -/
def uH4 : IV := (ImΩI.smul 480).add (piI.smul (2231 / 2))

lemma mem_uH4 : uH4.mem (480 * Ω.im + 2231 / 2 * π) := by
  have := mem_add (mem_smul 480 mem_ImΩI) (mem_smul (2231 / 2) mem_piI)
  push_cast at this; exact this

lemma chk_u : uH4.absLe (7 / 100) = true := by decide +kernel

/-- **(H4)** for I3: `sin(q · Im Ω) > 0.99` with `q = 480`. -/
theorem I3_sinqtheta_ge : 99 / 100 < Real.sin (480 * Ω.im) := by
  set u := 480 * Ω.im + 2231 / 2 * π with hu
  have hsin : Real.sin (480 * Ω.im) = Real.cos u := by
    rw [← Real.sin_add_pi_div_two, ← Real.sin_sub_nat_mul_two_pi (u + π / 2) 558]
    congr 1; rw [hu]; push_cast; ring
  rw [hsin]
  have h1 := abs_le_of_absLe mem_uH4 chk_u
  push_cast at h1
  have h2 := Real.one_sub_sq_div_two_le_cos (x := u)
  have h3 : u ^ 2 ≤ (7 / 100) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith

end BetaIrr.I3.Interval
