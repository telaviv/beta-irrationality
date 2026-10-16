/-
# The saddle data (S0)–(S5) for instance I3

`SaddleData` packages PROOF_BETA §6.3 (S0)–(S5) for instance I3 as finitely many `Prop`s about
the explicit phase `phaseI = Ψ - 2πix` (`I3/Analytic/Factors.lean`) and an explicit polyline
`v 0, …, v Ktop` (in `x = z/n` coordinates, `n = 480(m+1)`). Every field is a statement that
interval arithmetic can certify. Two fields carry the parameters:
* `H4 : sin(480 Im Ω) ≠ 0` (`q = 480`);
* `v0_lt : Re (v 0) < 7/6` (`r = 7/6`: the start `x_c` lies before the end `r` of the zero run).

The pointwise bounds (U), (M) that consume these fields are in `I3/Analytic/Pointwise.lean`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.Factors

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real Set

/-- **The saddle data (S0)–(S5) for I3.** All coordinates are `x = z/n`. -/
structure SaddleData where
  /-- the saddle point `x₀` -/
  x₀ : ℂ
  /-- the unit steepest-descent direction `d` -/
  d : ℂ
  /-- `K = |Ψ''(x₀)|` -/
  K : ℝ
  /-- `M ≥ sup |Ψ'''|` on the disc -/
  M : ℝ
  /-- disc radius (half-length of the disc segment) -/
  ρ : ℝ
  /-- polyline vertices `v 0 = x_c` (real), …, `v Ktop = x_top` -/
  v : ℕ → ℂ
  /-- the disc segment is `[v Kd, v (Kd+1)]` -/
  Kd : ℕ
  Ktop : ℕ
  /-- sector constants of (S4) -/
  a : ℝ
  η : ℝ
  /-- far-part margin of (S2), (S3) -/
  ηfar : ℝ
  /-- decay rate and threshold on the top ray (S3) -/
  rate : ℝ
  Y₀ : ℝ
  /-- tolerance for moving the start point `x_c` -/
  δ₀ : ℝ
  a_pos : 0 < a
  η_pos : 0 < η
  η_le : η ≤ π
  ηfar_pos : 0 < ηfar
  rate_pos : 0 < rate
  δ₀_pos : 0 < δ₀
  /-- (S0) `x₀` is a saddle: `f'(x₀) = Ψ'(x₀) - 2πi = 0`. -/
  S0 : Psi1I x₀ = 2 * π * I
  /-- (H4) `sin(480 Im Ω) ≠ 0`, `Ω = f(x₀)`. -/
  H4 : Real.sin (480 * (phaseI x₀).im) ≠ 0
  /-- (S1) Taylor disc. -/
  K_pos : 0 < K
  d_norm : ‖d‖ = 1
  S1_dir : Psi2I x₀ * d ^ 2 = -K
  ρ_pos : 0 < ρ
  S1_M : ∀ z ∈ Metric.closedBall x₀ ρ, ‖Psi3I z‖ ≤ M
  S1_ρ : M * ρ ≤ 3 * K / 2
  /-- (S1′) the disc lies in the upper half plane. -/
  S1'_disc : ρ < x₀.im
  /-- The path. -/
  Kd_pos : 1 ≤ Kd
  Kd_lt : Kd + 1 < Ktop + 1
  v_disc_lo : v Kd = x₀ - ρ * d
  v_disc_hi : v (Kd + 1) = x₀ + ρ * d
  v0_im : (v 0).im = 0
  δ₀_le : δ₀ ≤ (v 0).re
  v0_lt : (v 0).re < 7 / 6
  re_nonneg : ∀ k ≤ Ktop, 0 ≤ (v k).re
  top_re_pos : 0 < (v Ktop).re
  /-- (S1′) the path lies in the upper half plane except its start. -/
  path_im : ∀ k < Ktop, ∀ t ∈ Ioc (0 : ℝ) 1, 0 < (v k + t * (v (k + 1) - v k)).im
  /-- (S4) on the disc segment. -/
  S4_disc : ∀ s ∈ Icc (-ρ) ρ, SectorAt a η (x₀ + s * d)
  /-- (S2) + (S4) on the far polyline, segments `1 ≤ k < Ktop`, `k ≠ Kd`. -/
  S2 : ∀ k < Ktop, 1 ≤ k → k ≠ Kd → ∀ t ∈ Icc (0 : ℝ) 1,
    (phaseI (v k + t * (v (k + 1) - v k))).re ≤ (phaseI x₀).re - ηfar ∧
      SectorAt a η (v k + t * (v (k + 1) - v k))
  /-- (S2₀) + (S4) on the first segment, with start point moved by `|e| ≤ δ₀` along `ℝ`. -/
  S2_first : ∀ e ∈ Icc (-δ₀) δ₀, ∀ t ∈ Ioc (0 : ℝ) 1,
    (phaseI ((v 0 + e) + t * (v 1 - (v 0 + e)))).re ≤ (phaseI x₀).re - ηfar ∧
      SectorAt a η ((v 0 + e) + t * (v 1 - (v 0 + e)))
  /-- (S3) + (S4) on the top ray. -/
  S3 : ∀ y : ℝ, 0 ≤ y →
    (phaseI (v Ktop + y * I)).re ≤ (phaseI x₀).re - ηfar - rate * max 0 (y - Y₀) ∧
      SectorAt a η (v Ktop + y * I)

end BetaIrr.I3.Analytic
