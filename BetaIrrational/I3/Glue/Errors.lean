/-
# Glue (I3): the error terms of `log_D_sub_le` are `o(n)`

The error terms of Lemmas 4–5. With `n = 480(m+1)` and
`𝒩 = 3040(m+1) + 3 ≤ 7n`:
* `tendsto_err1`: the `p = 2` error `(40 + 123(⌊log₂ n⌋ + 1)) log 2 / n → 0`;
* `tendsto_err2`: the small-odd-prime error `312 ⌊√𝒩⌋ log 𝒩 / n → 0`.

(PROOF_BETA §4 "Size": these are the `o(n)` terms; the main term `20 n log 2` is kept apart.)

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Arith.Lemma4
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace BetaIrr.I3

open Filter Topology Finset Asymptotics

lemma nOf_pos (m : ℕ) : (0 : ℝ) < nOf m := by
  unfold nOf; positivity

lemma tendsto_nOf_atTop : Tendsto (fun m => (nOf m : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
  unfold nOf; push_cast; nlinarith

lemma tendsto_NN_atTop : Tendsto (fun m => (Arith.NN m : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
  unfold Arith.NN; push_cast; nlinarith

/-- The `p = 2` error: `(40 + 123(⌊log₂ n⌋ + 1)) log 2 / n → 0`. -/
lemma tendsto_err1 :
    Tendsto (fun m => (40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1)) * Real.log 2 / nOf m)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun m => Real.log (nOf m) / (nOf m : ℝ)) atTop (𝓝 0) := by
    have := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_nOf_atTop
    simpa [Function.comp_def] using this
  have hinv : Tendsto (fun m => 163 * Real.log 2 / (nOf m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_nOf_atTop
  have hup : Tendsto (fun m => 163 * Real.log 2 / (nOf m : ℝ) + 123 * (Real.log (nOf m) / nOf m))
      atTop (𝓝 0) := by
    simpa using hinv.add (hlog.const_mul 123)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun m => ?_) (fun m => ?_)
  · have := nOf_pos m
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  · have hn := nOf_pos m
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hb : ((Nat.log 2 (nOf m) : ℕ) : ℝ) ≤ Real.logb 2 (nOf m) :=
      Real.natLog_le_logb (nOf m) 2
    rw [Real.logb, le_div_iff₀ hl2] at hb
    change (40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1)) * Real.log 2 / nOf m
      ≤ 163 * Real.log 2 / (nOf m : ℝ) + 123 * (Real.log (nOf m) / nOf m)
    rw [mul_div_assoc', ← add_div]
    apply div_le_div_of_nonneg_right _ hn.le
    nlinarith

/-- The small-odd-prime error: `312 ⌊√𝒩⌋ log 𝒩 / n → 0` (`𝒩 = 3040(m+1)+3 ≤ 7n`). -/
lemma tendsto_err2 :
    Tendsto (fun m => 312 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m)
      atTop (𝓝 0) := by
  have hlo : Tendsto (fun m => Real.log (Arith.NN m) / (Arith.NN m : ℝ) ^ (1 / (2 : ℝ)))
      atTop (𝓝 0) := by
    have := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
      ).comp tendsto_NN_atTop
    simpa [Function.comp_def] using this
  have hup := hlo.const_mul 2184
  rw [mul_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun m => ?_) (fun m => ?_)
  · have := nOf_pos m
    have : 0 ≤ Real.log (Arith.NN m) := Real.log_natCast_nonneg _
    positivity
  · have hn := nOf_pos m
    set N : ℝ := (Arith.NN m : ℝ) with hNdef
    have hN : 0 < N := by rw [hNdef]; unfold Arith.NN; positivity
    have hN7 : N ≤ 7 * (nOf m : ℝ) := by rw [hNdef]; unfold Arith.NN nOf; push_cast; nlinarith
    have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg _
    have hs : ((Nat.sqrt (Arith.NN m) : ℕ) : ℝ) ≤ √N := Real.nat_sqrt_le_real_sqrt
    have hspos : 0 < √N := Real.sqrt_pos.mpr hN
    change 312 * ((Nat.sqrt (Arith.NN m) : ℕ) : ℝ) * Real.log N / nOf m
      ≤ 2184 * (Real.log N / N ^ (1 / (2 : ℝ)))
    rw [← Real.sqrt_eq_rpow, mul_div_assoc', div_le_div_iff₀ hn hspos]
    have h1 : 312 * ((Nat.sqrt (Arith.NN m) : ℕ) : ℝ) * Real.log N * √N
        ≤ 312 * √N * Real.log N * √N := by gcongr
    have hmul : √N * √N = N := Real.mul_self_sqrt hN.le
    have h2 : 312 * √N * Real.log N * √N = 312 * Real.log N * N := by
      calc 312 * √N * Real.log N * √N = 312 * Real.log N * (√N * √N) := by ring
        _ = 312 * Real.log N * N := by rw [hmul]
    nlinarith [mul_le_mul_of_nonneg_left hN7 (by positivity : (0 : ℝ) ≤ 312 * Real.log N)]

end BetaIrr.I3
