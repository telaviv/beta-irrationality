/-
# Lemma 6(i) for instance I3, real-axis version: the `size` field with `V_cert = -29.76`

**Theorem `BetaIrr.I3.size_I3`.** With `εL m = (A₀ + 22 log(m+1)) / (480(m+1)) → 0`, for every `m`,
`L_m ≠ 0 → log |L_m| ≤ -G log n! + n (V_cert + εL m)`, `n = 480(m+1)`, `V_cert = -29.76`,
where `A₀ = G (log 481 + 1) + 34 + 2 log 2 + 2 log 21642 + 2 log 1441`.

Proof (PROOF_BETA §8 Lemma 6(i), elementary real-axis route):
`|L_n| ≤ Σ_{t > rn} |R_n''(t)|` (`R2_eq_zero`: the terms `t ≤ rn` vanish), and for
`t ≥ rn + 1`, `|R_n''(t)| ≤ R_n(t)(M² + M)` (`abs_R2_le`) with
`log R_n(t) ≤ -G log n! + nΦ(t/n) + O(log n)` (`log_R_le_fact`). Then `Φ ≤ V_cert` on
`[r, ∞)` and `Φ(x) ≤ V_cert - 4 log(x/3)` for `x ≥ 3` (`PhiBound`) give a summable majorant
`K_m · 2(T+1)²/((t+1)(t+2))`, `T = 3n`.
Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Size.RBound
import BetaIrrational.I3.Size.R2Bound
import BetaIrrational.I3.Size.Vanish
import BetaIrrational.Size.Common

namespace BetaIrr.I3.Size

open Real Finset Filter Topology
open BetaIrr.Size (wt wt_nonneg summable_wt tsum_wt_le)

/-- The constant `C_m = -G log n! + G(log(n+1) + 1) + 34`. -/
noncomputable def Cst (m : ℕ) : ℝ :=
  -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (G : ℝ) * (Real.log ((nOf m : ℝ) + 1) + 1) + 34

/-- `T = 3n = 1440(m+1)`. -/
noncomputable def Tm (m : ℕ) : ℝ := 1440 * ((m : ℝ) + 1)

/-- The prefactor `K_m = (M² + M) e^{C_m + n V} · 2 (T+1)²`. -/
noncomputable def Km (m : ℕ) : ℝ :=
  (Mbd m ^ 2 + Mbd m) * Real.exp (Cst m + (nOf m : ℝ) * (Vcert : ℝ)) * (2 * (Tm m + 1) ^ 2)

lemma Mbd_pos (m : ℕ) : 0 < Mbd m := by unfold Mbd; positivity

lemma Km_pos (m : ℕ) : 0 < Km m := by
  unfold Km
  have := Mbd_pos m
  have : 0 < Tm m := by unfold Tm; positivity
  positivity

/-- `e^{nΦ(t/n)} ≤ e^{nV} · 2(T+1)² w(t)` for `t ≥ rn + 1`. -/
lemma exp_Phi_le (m t : ℕ) (ht : 560 * ((m : ℝ) + 1) + 1 ≤ t) :
    Real.exp ((nOf m : ℝ) * Phi (t / nOf m)) ≤
      Real.exp ((nOf m : ℝ) * (Vcert : ℝ)) * (2 * (Tm m + 1) ^ 2 * wt t) := by
  have hn : (nOf m : ℝ) = 480 * ((m : ℝ) + 1) := nOf_real m
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hnpos : (0 : ℝ) < nOf m := by rw [hn]; positivity
  have ht0 : (0 : ℝ) < t := by linarith
  have hx : 7 / 6 ≤ (t : ℝ) / nOf m := by rw [le_div_iff₀ hnpos, hn]; linarith
  have hT : Tm m = 3 * (nOf m : ℝ) := by rw [Tm, hn]; ring
  have hTpos : 0 < Tm m := by rw [hT]; positivity
  rcases le_or_gt (t : ℝ) (Tm m) with h | h
  · -- `t ≤ T`: weight factor at least one
    have h1 : Real.exp ((nOf m : ℝ) * Phi (t / nOf m)) ≤ Real.exp ((nOf m : ℝ) * (Vcert : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Phi_le_V hx) hnpos.le)
    have h2 : 1 ≤ 2 * (Tm m + 1) ^ 2 * wt t := by
      unfold wt
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h3 : 0 < Real.exp ((nOf m : ℝ) * (Vcert : ℝ)) := Real.exp_pos _
    nlinarith
  · -- `t > T`: tail decay
    have hx3 : 3 ≤ (t : ℝ) / nOf m := by rw [le_div_iff₀ hnpos]; linarith
    have hP := Phi_le_tail hx3
    have hq : (t : ℝ) / nOf m / 3 = t / Tm m := by rw [hT]; field_simp
    rw [hq] at hP
    have hlog : 0 ≤ Real.log (t / Tm m) := Real.log_nonneg (by rw [le_div_iff₀ hTpos]; linarith)
    have hn2 : (2 : ℝ) ≤ 4 * nOf m := by rw [hn]; nlinarith
    have hE : (nOf m : ℝ) * Phi (t / nOf m) ≤
        (nOf m : ℝ) * (Vcert : ℝ) - 2 * Real.log (t / Tm m) := by
      have := mul_le_mul_of_nonneg_left hP hnpos.le
      nlinarith
    have h1 := Real.exp_le_exp.mpr hE
    rw [Real.exp_sub] at h1
    have h2 : Real.exp (2 * Real.log (t / Tm m)) = (t / Tm m) ^ 2 := by
      rw [← Real.log_rpow (by positivity), Real.exp_log (by positivity)]
      norm_num
    rw [h2] at h1
    have h3 : 1 / (t / Tm m) ^ 2 ≤ 2 * (Tm m + 1) ^ 2 * wt t := by
      unfold wt
      rw [div_pow, one_div_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (Tm m) ^ 2 ≤ (Tm m + 1) ^ 2 := by nlinarith
      have h4 : ((t : ℝ) + 1) * ((t : ℝ) + 2) ≤ 2 * (t : ℝ) ^ 2 := by nlinarith
      nlinarith
    calc Real.exp ((nOf m : ℝ) * Phi (t / nOf m))
        ≤ Real.exp ((nOf m : ℝ) * (Vcert : ℝ)) / (t / Tm m) ^ 2 := h1
      _ = Real.exp ((nOf m : ℝ) * (Vcert : ℝ)) * (1 / (t / Tm m) ^ 2) := by ring
      _ ≤ Real.exp ((nOf m : ℝ) * (Vcert : ℝ)) * (2 * (Tm m + 1) ^ 2 * wt t) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le

/-- Pointwise majorant: `|R_n''(t)| ≤ K_m w(t)` for every `t ∈ ℕ`. -/
lemma abs_R2_le_wt (m t : ℕ) : |deriv (deriv (R m)) (t : ℝ)| ≤ Km m * wt t := by
  rcases le_or_gt t (560 * (m + 1)) with h | h
  · rw [R2_eq_zero m t h, abs_zero]
    exact mul_nonneg (Km_pos m).le (wt_nonneg t)
  · have ht : 560 * ((m : ℝ) + 1) + 1 ≤ t := by
      have : 560 * (m + 1) + 1 ≤ t := h
      exact_mod_cast this
    have h1 := abs_R2_le m t ht
    obtain ⟨hpos, h2⟩ := log_R_le_fact m t ht
    have h3 : R m t ≤ Real.exp (Cst m + (nOf m : ℝ) * Phi (t / nOf m)) := by
      rw [← Real.exp_log hpos]
      apply Real.exp_le_exp.mpr
      unfold Cst; linarith
    have h4 := exp_Phi_le m t ht
    rw [abs_of_pos hpos] at h1
    have hM : 0 ≤ Mbd m ^ 2 + Mbd m := by have := Mbd_pos m; positivity
    calc |deriv (deriv (R m)) (t : ℝ)| ≤ R m t * (Mbd m ^ 2 + Mbd m) := h1
      _ ≤ Real.exp (Cst m + (nOf m : ℝ) * Phi (t / nOf m)) * (Mbd m ^ 2 + Mbd m) :=
          mul_le_mul_of_nonneg_right h3 hM
      _ = (Mbd m ^ 2 + Mbd m) * Real.exp (Cst m) *
            Real.exp ((nOf m : ℝ) * Phi (t / nOf m)) := by rw [Real.exp_add]; ring
      _ ≤ (Mbd m ^ 2 + Mbd m) * Real.exp (Cst m) *
            (Real.exp ((nOf m : ℝ) * (Vcert : ℝ)) * (2 * (Tm m + 1) ^ 2 * wt t)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = Km m * wt t := by unfold Km; rw [Real.exp_add]; ring

/-- `|L_m| ≤ K_m`. -/
theorem abs_L_le (m : ℕ) : |L m| ≤ Km m := by
  have hle : ∀ t : ℕ, ‖(-1 : ℝ) ^ t * deriv (deriv (R m)) (t : ℝ)‖ ≤ Km m * wt t := by
    intro t
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    exact abs_R2_le_wt m t
  have hsum : Summable (fun t => Km m * wt t) := summable_wt.mul_left _
  have hs : Summable (fun t : ℕ => ‖(-1 : ℝ) ^ t * deriv (deriv (R m)) (t : ℝ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  calc |L m| = ‖∑' t : ℕ, (-1 : ℝ) ^ t * deriv (deriv (R m)) (t : ℝ)‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑' t : ℕ, ‖(-1 : ℝ) ^ t * deriv (deriv (R m)) (t : ℝ)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' t : ℕ, Km m * wt t := Summable.tsum_le_tsum hle hs hsum
    _ = Km m * ∑' t, wt t := tsum_mul_left
    _ ≤ Km m * 1 := mul_le_mul_of_nonneg_left tsum_wt_le (Km_pos m).le
    _ = Km m := mul_one _

/-- The constant `A₀` in the error term. -/
noncomputable def A0 : ℝ :=
  (G : ℝ) * (Real.log 481 + 1) + 34 + 2 * Real.log 2 + 2 * Real.log 21642 + 2 * Real.log 1441

/-- The error term `εL m = (A₀ + 22 log(m+1)) / (480 (m+1))`. -/
noncomputable def epsL (m : ℕ) : ℝ := (A0 + 22 * Real.log ((m : ℝ) + 1)) / (480 * ((m : ℝ) + 1))

lemma epsL_tendsto : Tendsto epsL atTop (𝓝 0) := by
  have hx : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 1 / (480 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 480 0 1 (by norm_num)
  have h2 : Tendsto (fun x : ℝ => A0 / (480 * x)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := A0)).div_atTop
      (tendsto_id.const_mul_atTop (show (0 : ℝ) < 480 by norm_num))
    simpa using this
  have h3 := (h2.add (h1.const_mul 22)).comp hx
  simp only [pow_one, add_zero, mul_zero] at h3
  refine h3.congr (fun m => ?_)
  simp only [Function.comp, epsL]
  ring

lemma log_Km_le (m : ℕ) : Real.log (Km m) ≤
    -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * ((Vcert : ℝ) + epsL m) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hn : (nOf m : ℝ) = 480 * ((m : ℝ) + 1) := nOf_real m
  have hM := Mbd_pos m
  have hT : 0 < Tm m := by unfold Tm; positivity
  unfold Km
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  -- the three logarithmic error terms
  have hlogm : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg hm1
  have e1 : Real.log (Mbd m ^ 2 + Mbd m) ≤
      Real.log 2 + 2 * Real.log 21642 + 2 * Real.log ((m : ℝ) + 1) := by
    have hb : Mbd m ^ 2 + Mbd m ≤ 2 * (21642 ^ 2 * ((m : ℝ) + 1) ^ 2) := by
      unfold Mbd; nlinarith
    calc Real.log (Mbd m ^ 2 + Mbd m) ≤ Real.log (2 * (21642 ^ 2 * ((m : ℝ) + 1) ^ 2)) :=
          Real.log_le_log (by positivity) hb
      _ = _ := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity),
            Real.log_pow, Real.log_pow]
          push_cast; ring
  have e2 : Real.log (Tm m + 1) ≤ Real.log 1441 + Real.log ((m : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by unfold Tm; nlinarith)
  have e3 : Real.log ((nOf m : ℝ) + 1) ≤ Real.log 481 + Real.log ((m : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by rw [hn]; nlinarith)
  have hG : (G : ℝ) = 179 / 10 := by norm_num [G]
  have hneps : (nOf m : ℝ) * epsL m = A0 + 22 * Real.log ((m : ℝ) + 1) := by
    unfold epsL; rw [hn]; field_simp
  unfold Cst
  have hsplit : (nOf m : ℝ) * ((Vcert : ℝ) + epsL m) =
      (nOf m : ℝ) * (Vcert : ℝ) + (A0 + 22 * Real.log ((m : ℝ) + 1)) := by
    rw [mul_add, hneps]
  rw [hsplit]
  unfold A0
  rw [hG]
  push_cast
  linarith [e1, e2, e3, hlogm]

end BetaIrr.I3.Size

namespace BetaIrr.I3

open Filter Topology

/-- The explicit error term of Lemma 6(i) for I3:
`εL m = (A₀ + 22 log(m+1)) / (480 (m+1))`, `A₀ = G(log 481 + 1) + 34 + 2 log 2 + 2 log 21642 + 2 log 1441`. -/
noncomputable def εL : ℕ → ℝ := Size.epsL

lemma εL_lim : Tendsto εL atTop (𝓝 0) := Size.epsL_tendsto

/-- **Lemma 6(i) for I3, real-axis version**, with `V_cert = -29.76`. -/
theorem size_I3 : ∀ m, L m ≠ 0 →
    Real.log |L m| ≤ -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) +
      (nOf m : ℝ) * ((Vcert : ℝ) + εL m) := by
  intro m hL
  calc Real.log |L m| ≤ Real.log (Size.Km m) :=
        Real.log_le_log (abs_pos.mpr hL) (Size.abs_L_le m)
    _ ≤ _ := Size.log_Km_le m

end BetaIrr.I3
