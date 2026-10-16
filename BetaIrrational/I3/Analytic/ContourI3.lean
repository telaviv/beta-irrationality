/-
# `L_n` as a contour integral (PROOF_BETA §6.1 for the concrete I3 form)

Mirrors `Analytic/ConcreteContour.lean`.

`L_eq_half_line`: for every non-integer `c ∈ (0, 560(m+1) + 1)`,

    I3.L m = -(1/π) Re ∫_0^∞ R_n''(c + iy) π / sin(π(c + iy)) dy,

i.e. `L_n = -(1/π) Im ∫_c^{c+i∞} F_n(z) dz`. This combines the abstract contour formula
`hasSum_alternating_eq_half_line` with the concrete facts A1–A5 (`ConcreteIntegrand.lean`,
`ConcreteBound.lean`).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.Bound

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real MeasureTheory Set Filter Topology
open BetaIrr.Analytic BetaIrr.Fam.Analytic


/-- `F_n(z) = R_n''(z) π / sin(π z)`. -/
noncomputable def Fn (m : ℕ) : ℂ → ℂ := Fker (fC m)

/-- **`L_n` as a half-line integral.** -/
theorem L_eq_half_line (m : ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 560 * ((m : ℝ) + 1) + 1)
    (hcZ : ∀ k : ℤ, c ≠ k) :
    I3.L m = -(1 / π) * (∫ y in Ioi (0 : ℝ), Fn m (c + y * I)).re := by
  obtain ⟨C, hC⟩ := fC_bound m (c := c) (by linarith)
  have hdiff : DifferentiableOn ℂ (fC m) {z : ℂ | -1 / 2 < z.re} := fun z hz =>
    (fC_differentiableAt m (fun hp => by
      have := re_le_of_mem_poles hp
      simp only [Set.mem_ofPred_eq] at hz
      linarith)).differentiableWithinAt
  have hz : ∀ t : ℕ, (t : ℝ) < c → fC m t = 0 := by
    intro t ht
    apply fC_nat_zero
    have : (t : ℝ) < 560 * ((m : ℝ) + 1) + 1 := ht.trans hc1
    have : (t : ℝ) < ((560 * (m + 1) + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 this
    omega
  have hconj : ∀ y : ℝ, fC m (c + (-y : ℝ) * I) = (starRingEnd ℂ) (fC m (c + y * I)) := by
    intro y
    have hnp : (c : ℂ) + y * I ∉ poles m := fun hp => by
      have := re_le_of_mem_poles hp
      simp at this
      linarith
    rw [← fC_conj m hnp]
    congr 1
    apply Complex.ext <;> simp
  have hsum := hasSum_alternating_eq_half_line (c₀ := -1 / 2) hdiff hC (by linarith)
    (by linarith) hcZ hz hconj
  have hre := Complex.hasSum_re hsum
  simp only [Complex.ofReal_re] at hre
  have hterm : (fun t : ℕ => ((-1 : ℂ) ^ t * fC m t).re)
      = fun t : ℕ => (-1 : ℝ) ^ t * deriv (deriv (I3.R m)) t := by
    funext t
    rw [← fC_re_eq m t (by have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith)]
    rw [show ((-1 : ℂ) ^ t) = (((-1 : ℝ) ^ t : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    rfl
  rw [hterm] at hre
  unfold I3.L
  rw [hre.tsum_eq]
  rfl

end BetaIrr.I3.Analytic
