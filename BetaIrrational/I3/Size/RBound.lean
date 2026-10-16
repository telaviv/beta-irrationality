/-
# Real-axis size of the I3 `R_n(t)` for `t ≥ rn + 1`

For real `t ≥ 560(m+1) + 1 = rn + 1` (with `n = 480(m+1)`), `R_n(t) > 0` and

  `log R_n(t) ≤ n Φ(t/n) - G n (log n - 1) + 34`                (`log_R_le`)
  `log R_n(t) ≤ -G log n! + n Φ(t/n) + G (log(n+1) + 1) + 34`   (`log_R_le_fact`).

Proof: `log R_n` is a sum of `log`s over runs of consecutive
integers / half-integers; compare each run with `F(y) = y log y` (`Runs.lean`). The `n log n`
terms combine to `-G n log n` because `3(1 + 2r) - Σ m_j (1 - 2δ_j) = 10 - 27.9 = -G`. The leftover
logarithms are `7 log 3 + 35 log 2 - 28 log t ≤ 34`.
Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Size.Runs
import BetaIrrational.I3.Size.PhiBound
import BetaIrrational.Size.Common

namespace BetaIrr.I3.Size

open Real Finset
open BetaIrr.Size (F log_factorial_le list_sum_le list_sum_lin)

lemma nOf_real (m : ℕ) : (nOf m : ℝ) = 480 * ((m : ℝ) + 1) := by
  simp [nOf]

/-- Positivity and the explicit log of `R_n(t)` for `t > rn`. -/
lemma R_pos_and_log (m : ℕ) (t : ℝ) (ht : 560 * ((m : ℝ) + 1) < t) :
    0 < R m t ∧ Real.log (R m t) = Real.log (2 * t + (nOf m : ℝ) + 1) +
      3 * ∑ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)), Real.log (t - (l : ℝ)) -
      (blocks.map (fun b => (b.2 : ℝ) * ∑ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
        Real.log (t + (k : ℝ) + 1 / 2))).sum := by
  have ht0 : 0 < t := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hlin : 0 < 2 * t + (nOf m : ℝ) + 1 := by positivity
  have hl : ∀ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)), 0 < t - (l : ℝ) := by
    intro l hl
    have := (mem_Icc.mp hl).2
    have : (l : ℝ) ≤ 560 * ((m : ℝ) + 1) := by exact_mod_cast this
    linarith
  have hk : ∀ k : ℕ, 0 < t + (k : ℝ) + 1 / 2 := fun k => by positivity
  have hP : 0 < ∏ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)), (t - (l : ℝ)) ^ 3 :=
    prod_pos (fun l hl' => pow_pos (hl l hl') 3)
  have hblock : ∀ b : ℕ × ℕ, 0 < (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
      (t + (k : ℝ) + 1 / 2)) ^ b.2 := fun b => pow_pos (prod_pos (fun k _ => hk k)) _
  have hD : ∀ l : List (ℕ × ℕ), 0 < (l.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
        (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.prod_cons]; exact mul_pos (hblock a) ih
  have hDlog : ∀ l : List (ℕ × ℕ), Real.log ((l.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
        (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod) =
      (l.map (fun b => (b.2 : ℝ) * ∑ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
        Real.log (t + (k : ℝ) + 1 / 2))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [Real.log_mul (hblock a).ne' (hD l).ne', ih, Real.log_pow,
        Real.log_prod (fun k _ => (hk k).ne')]
  refine ⟨?_, ?_⟩
  · unfold R; exact div_pos (mul_pos hlin hP) (hD _)
  · unfold R
    have h3 : ∑ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)),
        Real.log ((t - (l : ℝ)) ^ 3) =
        3 * ∑ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)), Real.log (t - (l : ℝ)) := by
      rw [mul_sum]
      refine sum_congr rfl (fun l _ => ?_)
      rw [Real.log_pow]; push_cast; ring
    rw [Real.log_div (mul_pos hlin hP).ne' (hD _).ne', Real.log_mul hlin.ne' hP.ne', hDlog,
      Real.log_prod (fun l hl' => (pow_pos (hl l hl') 3).ne'), h3]

/-- **Real-axis bound for `R_n(t)`.** -/
theorem log_R_le (m : ℕ) (t : ℝ) (ht : 560 * ((m : ℝ) + 1) + 1 ≤ t) :
    0 < R m t ∧ Real.log (R m t) ≤ (nOf m : ℝ) * Phi (t / nOf m) -
      (G : ℝ) * (nOf m : ℝ) * (Real.log (nOf m) - 1) + 34 := by
  obtain ⟨hpos, hlog⟩ := R_pos_and_log m t (by linarith)
  refine ⟨hpos, ?_⟩
  rw [hlog]
  set K : ℝ := (m : ℝ) + 1 with hK
  have hK1 : 1 ≤ K := by simp [hK]
  have hn : (nOf m : ℝ) = 480 * K := nOf_real m
  have ht1 : 1 ≤ t := by nlinarith
  have hnum := num_run_le (m + 1) (by omega) t (by push_cast; linarith)
  push_cast at hnum
  rw [← hK, ← hn] at hnum
  -- denominator: blockwise lower bound, summed
  have hden := list_sum_le blocks
    (fun b => (b.2 : ℝ) * ((nOf m : ℝ) * (F (t / nOf m + 1 - (b.1 : ℝ) / 160) -
        F (t / nOf m + (b.1 : ℝ) / 160)) +
      (nOf m : ℝ) * (Real.log (nOf m) - 1) * (1 - 2 * ((b.1 : ℝ) / 160)) +
      (Real.log t - Real.log 2)))
    (fun b => (b.2 : ℝ) * ∑ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
        Real.log (t + (k : ℝ) + 1 / 2)) (by
      intro b hb
      have h9 : b.1 ≤ 80 := (blk_le b hb).trans (by norm_num)
      have := block_run_ge (m + 1) (by omega) t (by push_cast; linarith) b.1 h9
      have e : nOf m - 3 * b.1 * (m + 1) = 480 * (m + 1) - 3 * b.1 * (m + 1) := rfl
      rw [e]
      push_cast at this
      rw [← hK, ← hn] at this
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith)
  rw [list_sum_lin] at hden
  have hS : (blocks.map (fun b => (b.2 : ℝ))).sum = 35 := by
    simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; norm_num
  have hS2 : (blocks.map (fun b => (b.2 : ℝ) * (1 - 2 * ((b.1 : ℝ) / 160)))).sum = 279 / 10 := by
    simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; norm_num
  rw [hS, hS2] at hden
  -- Φ in terms of the block sum
  have hPhi : (nOf m : ℝ) * Phi (t / nOf m) = (nOf m : ℝ) * (3 * F (t / nOf m + 13 / 6) -
      3 * F (t / nOf m - 7 / 6)) - (nOf m : ℝ) * (blocks.map (fun b => (b.2 : ℝ) *
        (F (t / nOf m + 1 - (b.1 : ℝ) / 160) - F (t / nOf m + (b.1 : ℝ) / 160)))).sum := by
    unfold Phi; ring
  -- the leftover logarithms
  have hl1 : Real.log (2 * t + (nOf m : ℝ) + 1) ≤ Real.log 3 + Real.log t := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by rw [hn]; nlinarith)
  have hl2 : Real.log (t + 1040 * K + 2) ≤ Real.log 3 + Real.log t := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have l2 := Real.log_two_lt_d9
  have l3 := Real.log_three_lt_d9
  have hG : (G : ℝ) = 179 / 10 := by norm_num [G]
  rw [hG]
  norm_num at l2 l3
  nlinarith

/-- **Real-axis bound for `R_n(t)`, factorial form.** -/
theorem log_R_le_fact (m : ℕ) (t : ℝ) (ht : 560 * ((m : ℝ) + 1) + 1 ≤ t) :
    0 < R m t ∧ Real.log (R m t) ≤ -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) +
      (nOf m : ℝ) * Phi (t / nOf m) + (G : ℝ) * (Real.log ((nOf m : ℝ) + 1) + 1) + 34 := by
  obtain ⟨hpos, h⟩ := log_R_le m t ht
  refine ⟨hpos, ?_⟩
  have hf := log_factorial_le (nOf m)
  have hG : (0 : ℝ) ≤ (G : ℝ) := by norm_num [G]
  nlinarith

end BetaIrr.I3.Size
