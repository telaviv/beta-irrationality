/-
# The top ray of the I3 contour: (S3) and (S4) (PROOF_BETA §6.3)

The contour ends with the vertical ray `X0 + i y`, `y ≥ Im xtop ≈ 60.012`, `X0 = Re xtop ≈ 9.2117`.

* **(S3)** `S3_ray`: `Im Ψ'(X0 + i y) ≥ q0 = 7` for all `y ≥ Im xtop`: box checks on
  `[60.012, 90.019]`, `[90.019, 180.038]`, `[180.038, 900.19]` (`chk_ray`), and beyond `900.19` the
  analytic tail `Im Ψ' ≥ (π/2) Σ c - Σ |c| |s X0 + κ| / y = 3π - 738.09…/y` (`im_dpsiL_ge_tail`,
  `Σ c = 6`). Hence `∂h/∂y = 2π - Im Ψ' ≤ -(q0 - 2π) < -0.71` (`S3_h_decreasing`,
  `q0_sub_two_pi`).
* **(S4)** `S4_ray`: `|α_i| ≥ 60 ≥ 1/1000` and `|arg α_i| ≤ π/2 + 13/60 ≤ 2.76` on the ray;
  `S4_ray_efactor`: `Re(2z + 1) > 0`.

All numerical checks are `decide +kernel` (no `native_decide`).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Interval.PolyDataI3

namespace BetaIrr.I3.Interval

open Complex Metric BetaIrr.Interval BetaIrr.Interval.IV Real

def X0 : ℚ := xtop.1
def q0 : ℚ := 7
def rayYs : List ℚ := [90019 / 1000, 90019 / 500, 90019 / 100]

lemma chk_ray : rayPts 40 16 facI3 X0 q0 (xtop.2 :: rayYs) = true := by decide +kernel

lemma chk_tail : q0 ≤ 3 * (314 / 100) - tailB X0 facI3 / (90019 / 100) := by decide +kernel

lemma chk_tail0 : (0 : ℚ) ≤ tailB X0 facI3 := by decide +kernel

lemma csum_facI3 : csum facI3 = 6 := by decide +kernel

/-- **(S3)** `Im Ψ' ≥ q0` on the whole top ray `Re z = X0`, `Im z ≥ Im xtop`. -/
theorem S3_ray (y : ℝ) (hy : (xtop.2 : ℝ) ≤ y) : (q0 : ℝ) ≤ (dpsiL facI3 ⟨X0, y⟩).im := by
  rcases le_total y ((90019 / 100 : ℚ) : ℝ) with h | h
  · exact ray_pts 40 16 facI3 X0 q0 xtop.2 _ _ chk_ray y hy (by simpa [rayYs] using h)
  · have hY0 : (0 : ℝ) < ((90019 / 100 : ℚ) : ℝ) := by norm_num
    have hy0 : (0 : ℝ) < y := hY0.trans_le h
    have ht := im_dpsiL_ge_tail facI3 facI3_s1 X0 (z := ⟨X0, y⟩) rfl hy0
    rw [csum_facI3] at ht
    have hpi := Real.pi_gt_d2
    have hT : (0 : ℝ) ≤ (tailB X0 facI3 : ℝ) := by exact_mod_cast chk_tail0
    have hdiv : (tailB X0 facI3 : ℝ) / y ≤ (tailB X0 facI3 : ℝ) / ((90019 / 100 : ℚ) : ℝ) :=
      div_le_div_of_nonneg_left hT hY0 h
    have hc : (q0 : ℝ) ≤ ((3 * (314 / 100) - tailB X0 facI3 / (90019 / 100) : ℚ) : ℝ) := by
      exact_mod_cast chk_tail
    push_cast at hc ht hdiv ⊢
    linarith

lemma ray_eq (y : ℝ) : ((X0 : ℝ) : ℂ) + (y : ℂ) * I = ⟨X0, y⟩ := by
  apply Complex.ext <;> simp

lemma xtop2_pos : (0 : ℝ) < (xtop.2 : ℝ) := by simp [xtop]

lemma ray_good (y : ℝ) (hy : (xtop.2 : ℝ) ≤ y) : Good facI3 (((X0 : ℝ) : ℂ) + (y : ℂ) * I) := by
  apply good_of_im
  rw [ray_eq]
  have := xtop2_pos
  simp only [ne_eq]
  intro h; change y = 0 at h; linarith

/-- `h` decreases along the top ray at rate `q0 - 2π > 0.71`. -/
theorem S3_h_decreasing {y1 y2 : ℝ} (h1 : (xtop.2 : ℝ) ≤ y1) (h12 : y1 ≤ y2) :
    (f ⟨X0, y2⟩).re ≤ (f ⟨X0, y1⟩).re - (q0 - 2 * π) * (y2 - y1) := by
  have := ray_h_decreasing facI3 X0 xtop.2 (q0 - 2 * π) (fun y hy => ray_good y hy)
    (fun y hy => by rw [ray_eq]; linarith [S3_ray y hy]) h1 h12
  rw [ray_eq, ray_eq] at this
  exact this

theorem q0_sub_two_pi : (71 / 100 : ℝ) < q0 - 2 * π := by
  have := Real.pi_lt_d4; norm_num [q0]; linarith

lemma re_bound : ∀ b ∈ facI3, |(b.s : ℚ) * X0 + b.κ| ≤ 13 := by decide +kernel

/-- **(S4) on the ray.** -/
theorem S4_ray (y : ℝ) (hy : (xtop.2 : ℝ) ≤ y) :
    ∀ a ∈ facI3, (amin : ℝ) ≤ ‖a.α ⟨X0, y⟩‖ ∧ |arg (a.α ⟨X0, y⟩)| ≤ Amax := by
  intro a ha
  have hy60 : (60 : ℝ) ≤ y := le_trans (by simp [xtop]; norm_num) hy
  have hs := facI3_s1 a ha
  have hre : |(a.α ⟨X0, y⟩).re| ≤ 13 := by
    have := re_bound a ha
    have e : (a.α ⟨X0, y⟩).re = (((a.s : ℚ) * X0 + a.κ : ℚ) : ℝ) := by simp [Fac.α]
    rw [e]; exact_mod_cast this
  have him : |(a.α ⟨X0, y⟩).im| = y := by
    rcases hs with h | h <;> simp [Fac.α, h, abs_of_pos (by linarith : (0 : ℝ) < y)]
  constructor
  · calc ((amin : ℚ) : ℝ) ≤ 60 := by norm_num
      _ ≤ |(a.α ⟨X0, y⟩).im| := by rw [him]; exact hy60
      _ ≤ ‖a.α ⟨X0, y⟩‖ := Complex.abs_im_le_norm _
  · have hat : |Real.arctan ((a.α ⟨X0, y⟩).re / (a.α ⟨X0, y⟩).im)| ≤ 13 / 60 := by
      refine Real.abs_arctan_le_abs.trans ?_
      rw [abs_div, him, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [abs_nonneg (a.α ⟨X0, y⟩).re]
    have hpi := Real.pi_lt_d2
    have hpi' := Real.pi_gt_three
    rcases hs with h | h
    · have hp : 0 < (a.α ⟨X0, y⟩).im := by simp [Fac.α, h]; linarith
      rw [arg_eq_of_im_pos hp]
      rw [abs_le] at hat ⊢
      constructor <;> norm_num [Amax] <;> linarith [hat.1, hat.2]
    · have hn : (a.α ⟨X0, y⟩).im < 0 := by simp [Fac.α, h]; linarith
      rw [arg_eq_of_im_neg hn]
      rw [abs_le] at hat ⊢
      constructor <;> norm_num [Amax] <;> linarith [hat.1, hat.2]

theorem S4_ray_efactor (y : ℝ) : 0 < (2 * (⟨X0, y⟩ : ℂ) + 1).re := by
  simp [X0, xtop]; norm_num

end BetaIrr.I3.Interval
