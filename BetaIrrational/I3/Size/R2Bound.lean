/-
# `|R_n''(t)| ≤ R_n(t) (M² + M)` for `t ≥ rn + 1` (instance I3)

`R_n = (2t + n + 1) Π_l (t - l)^3 / Π_j Π_k (t + k + 1/2)^{m_j}`. For `t ≥ rn + 1` every zero and
pole is at distance `≥ 1`, so the logarithmic-derivative bound of `Size/LogDeriv.lean` applies with
`M = 1 + 3·#zeros + Σ_j m_j #poles_j ≤ 1 + 3(1600(m+1) + 2) + 35(480(m+1) + 1) ≤ 21642(m+1)`.
Status: complete (no `sorry`).
-/
import BetaIrrational.FamilyI3
import BetaIrrational.Size.LogDeriv
import BetaIrrational.I3.Size.Phi

namespace BetaIrr.I3.Size

open Real Finset
open BetaIrr.Size (LD list_sum_le)

/-- The multiplicity bound `M_m = 21642 (m+1)`. -/
noncomputable def Mbd (m : ℕ) : ℝ := 21642 * ((m : ℝ) + 1)

theorem abs_R2_le (m : ℕ) (t₀ : ℝ) (ht : 560 * ((m : ℝ) + 1) + 1 ≤ t₀) :
    |deriv (deriv (R m)) t₀| ≤ |R m t₀| * (Mbd m ^ 2 + Mbd m) := by
  set U : Set ℝ := Set.Ioi (560 * ((m : ℝ) + 1) + 1 / 2) with hU
  have hUo : IsOpen U := isOpen_Ioi
  have ht₀ : t₀ ∈ U := by simp only [hU, Set.mem_Ioi]; linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hUpos : ∀ t ∈ U, 560 * ((m : ℝ) + 1) + 1 / 2 < t := fun t ht => ht
  -- the linear factor
  have hA : LD (fun t => 2 * t + (nOf m : ℝ) + 1) U t₀ 1 := by
    refine (LD.affine 2 ((nOf m : ℝ) + 1) (fun t ht => ?_) ht₀ ?_).of_eq (fun t => by ring)
    · have := hUpos t ht
      have : (0 : ℝ) ≤ nOf m := Nat.cast_nonneg _
      intro h; linarith
    · have : (0 : ℝ) ≤ nOf m := Nat.cast_nonneg _
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by linarith)]
      linarith
  -- the zero factors
  have hP : LD (fun t => ∏ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)),
      (t - (l : ℝ)) ^ 3) U t₀
      ((Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1))).card * ((3 : ℕ) * 1)) := by
    apply LD.finset_prod
    intro l hl
    have hl' : (l : ℝ) ≤ 560 * ((m : ℝ) + 1) := by
      have := (mem_Icc.mp hl).2
      exact_mod_cast this
    refine ((LD.affine 1 (-(l : ℝ)) (fun t ht => ?_) ht₀ ?_).of_eq (fun t => by ring)).pow 3
    · have := hUpos t ht; intro h; linarith
    · rw [abs_one, abs_of_pos (by linarith)]; linarith
  -- the pole factors
  have hk : ∀ (k : ℕ), LD (fun t => t + (k : ℝ) + 1 / 2) U t₀ 1 := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine (LD.affine 1 ((k : ℝ) + 1 / 2) (fun t ht => ?_) ht₀ ?_).of_eq (fun t => by ring)
    · have := hUpos t ht; intro h; linarith
    · rw [abs_one, abs_of_pos (by linarith)]; linarith
  have hD : LD (fun t => (blocks.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)), (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod)
      U t₀ (blocks.map (fun b => (b.2 : ℝ) *
        ((Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1))).card * 1))).sum := by
    apply LD.list_prod
    intro b _
    exact (LD.finset_prod _ _ (fun k _ => hk k)).pow b.2
  have hne : ∀ t ∈ U, (blocks.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)), (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod
        ≠ 0 := by
    intro t ht
    have htp : 0 < t := by have := hUpos t ht; linarith
    have : ∀ l : List (ℕ × ℕ), 0 < (l.map (fun b =>
        (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
          (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.prod_cons]
        exact mul_pos (pow_pos (prod_pos (fun k _ => by positivity)) _) ih
    exact (this blocks).ne'
  have hR := (hA.mul hP).div hD hne
  -- bound the total multiplicity
  have hcard1 : ((Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1))).card : ℝ) =
      1600 * ((m : ℝ) + 1) + 2 := by
    rw [Int.card_Icc]
    have : 560 * ((m : ℤ) + 1) + 1 - (-(1040 * ((m : ℤ) + 1)) - 1) =
        ((1600 * (m + 1) + 2 : ℕ) : ℤ) := by
      push_cast; ring
    rw [this, Int.toNat_natCast]
    push_cast; ring
  have hcard2 : ∀ b : ℕ × ℕ,
      ((Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1))).card : ℝ) ≤ 480 * ((m : ℝ) + 1) + 1 := by
    intro b
    rw [Nat.card_Icc]
    have : nOf m - 3 * b.1 * (m + 1) + 1 - 3 * b.1 * (m + 1) ≤ 480 * (m + 1) + 1 := by
      unfold nOf; omega
    have := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at this
    exact this
  have hsum : (blocks.map (fun b => (b.2 : ℝ) *
      ((Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1))).card * 1))).sum ≤
      35 * (480 * ((m : ℝ) + 1) + 1) := by
    have := list_sum_le blocks
      (fun b => (b.2 : ℝ) * ((Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1))).card * 1))
      (fun b => (b.2 : ℝ) * (480 * ((m : ℝ) + 1) + 1)) (fun b _ => by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [mul_one]; exact hcard2 b)
    rw [List.sum_map_mul_right] at this
    have hS : (blocks.map (fun b => (b.2 : ℝ))).sum = 35 := by
      simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; norm_num
    rw [hS] at this
    exact this
  have hM : 1 + ((Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1))).card * ((3 : ℕ) * 1)) +
      (blocks.map (fun b => (b.2 : ℝ) *
        ((Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1))).card * 1))).sum ≤ Mbd m := by
    rw [hcard1, Mbd]
    push_cast
    nlinarith
  have hR' := (hR.mono hM).abs_deriv2_le hUo ht₀
  have e : R m = fun t => (2 * t + (nOf m : ℝ) + 1) *
      (∏ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)), (t - (l : ℝ)) ^ 3) /
      (blocks.map (fun b =>
        (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)), (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod
    := rfl
  rw [e]
  exact hR'

end BetaIrr.I3.Size
