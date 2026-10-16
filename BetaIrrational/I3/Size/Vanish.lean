/-
# `R_n''` vanishes at the triple zeros `t = 0, 1, …, rn` (instance I3)

For the I3 `R_n`, every integer `l₀ ∈ [0, rn] = [0, 560(m+1)]` is a zero of multiplicity 3 and the
cofactor is smooth on `t > -1/2` (the poles are at negative half-integers), so
`R_n''(l₀) = 0` by the generic `deriv2_cube_mul_eq_zero` of `Size/Common.lean`.
Status: complete (no `sorry`).
-/
import BetaIrrational.FamilyI3
import BetaIrrational.Size.Common

namespace BetaIrr.I3.Size

open Real Finset Filter Topology
open BetaIrr.Size (deriv2_cube_mul_eq_zero contDiff_list_prod)

/-- **`R_n''(l₀) = 0` for the integers `0 ≤ l₀ ≤ rn = 560(m+1)`.** -/
theorem R2_eq_zero (m l₀ : ℕ) (hl : l₀ ≤ 560 * (m + 1)) :
    deriv (deriv (R m)) (l₀ : ℝ) = 0 := by
  set S := Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)) with hS
  set D : ℝ → ℝ := fun t => (blocks.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)), (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod
    with hD
  have hmem : (l₀ : ℤ) ∈ S := by
    rw [hS, mem_Icc]; constructor <;> omega
  set hf : ℝ → ℝ := fun t => (2 * t + (nOf m : ℝ) + 1) *
      (∏ l ∈ S.erase (l₀ : ℤ), (t - (l : ℝ)) ^ 3) / D t with hhf
  have hR : R m = fun t => (t - (l₀ : ℝ)) ^ 3 * hf t := by
    funext t
    simp only [R, hhf, hD]
    rw [← hS, ← Finset.mul_prod_erase S _ hmem]
    push_cast
    ring
  rw [hR]
  have hU : IsOpen (Set.Ioi (-1 / 2 : ℝ)) := isOpen_Ioi
  have ha : (l₀ : ℝ) ∈ Set.Ioi (-1 / 2 : ℝ) := by
    simp only [Set.mem_Ioi]; have : (0 : ℝ) ≤ l₀ := Nat.cast_nonneg _; linarith
  apply deriv2_cube_mul_eq_zero hU ha
  have hnum : ContDiff ℝ 2 (fun t => (2 * t + (nOf m : ℝ) + 1) *
      (∏ l ∈ S.erase (l₀ : ℤ), (t - (l : ℝ)) ^ 3)) := by
    fun_prop
  have hDc : ContDiff ℝ 2 D := by
    apply contDiff_list_prod
    intro b _
    fun_prop
  have hDne : ∀ t ∈ Set.Ioi (-1 / 2 : ℝ), D t ≠ 0 := by
    intro t ht
    have ht : -1 / 2 < t := ht
    have : ∀ l : List (ℕ × ℕ), 0 < (l.map (fun b =>
        (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
          (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.prod_cons]
        refine mul_pos (pow_pos (prod_pos (fun k _ => ?_)) _) ih
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
    exact (this blocks).ne'
  exact hnum.contDiffOn.div hDc.contDiffOn hDne

end BetaIrr.I3.Size
