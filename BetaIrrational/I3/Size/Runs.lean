/-
# The numerator and denominator runs of the I3 `R_n`, compared with `n Φ`

Write `n = 480 K`, `rn = 560 K`, `(1+r)n = 1040 K` (`K = m + 1`), `x = t/n`, `t ≥ 560K + 1`.

* `num_run_le`: `Σ_{l=-1040K-1}^{560K} log(t - l) ≤ n[F(x+13/6) - F(x-7/6)] + (10/3) n (log n - 1)
  + 2 log(t + 1040K + 2)`.
* `block_run_ge`: for `k ≤ 80`, `Σ_{j=3kK}^{480K-3kK} log(t + j + 1/2) ≥ n[F(x+1-δ) - F(x+δ)]
  + n(1 - 2δ)(log n - 1) + log t - log 2`, `δ = k/160`.

The run comparisons themselves are the generic lemmas of `Size/Discrete.lean`.
Status: complete (no `sorry`).
-/
import BetaIrrational.Size.Discrete

namespace BetaIrr.I3.Size

open Real Finset
open BetaIrr.Size (F F_tangent F_scale sum_log_int_le sum_log_half_ge)

/-- Per block: the denominator run is at least its continuum value. -/
lemma block_run_ge (K : ℕ) (hK : 1 ≤ K) (t : ℝ) (ht : 560 * (K : ℝ) + 1 ≤ t) (d : ℕ)
    (hd : d ≤ 80) :
    (480 * (K : ℝ)) * (F (t / (480 * K) + 1 - (d : ℝ) / 160) - F (t / (480 * K) + (d : ℝ) / 160)) +
      (480 * (K : ℝ)) * (1 - 2 * ((d : ℝ) / 160)) * (Real.log (480 * K) - 1) +
      (Real.log t - Real.log 2) ≤
    ∑ k ∈ Icc (3 * d * K) (480 * K - 3 * d * K), Real.log (t + (k : ℝ) + 1 / 2) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hd9 : (d : ℝ) ≤ 80 := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hnpos : (0 : ℝ) < 480 * K := by positivity
  have hle : 6 * d * K ≤ 480 * K := by nlinarith
  have hIcc : 480 * K - 3 * d * K = 3 * d * K + (480 * K - 6 * d * K) := by
    have h3 : 3 * d * K = 3 * (d * K) := by ring
    have h6 : 6 * d * K = 6 * (d * K) := by ring
    rw [h6] at hle
    rw [h3, h6]
    omega
  have hAr : ((3 * d * K : ℕ) : ℝ) = 3 * d * K := by push_cast; ring
  have hjr : ((480 * K - 6 * d * K : ℕ) : ℝ) = 480 * K - 6 * d * K := by
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [hIcc]
  have hrun := sum_log_half_ge t (3 * d * K) (480 * K - 6 * d * K) (by rw [hAr]; nlinarith)
  have hAj : ((3 * d * K + (480 * K - 6 * d * K) : ℕ) : ℝ) = 480 * K - 3 * d * K := by
    push_cast; rw [hjr]; ring
  rw [hAj, hAr, hjr] at hrun
  -- endpoint shifts
  have hB0 : 0 < t + (480 * K - 3 * d * K) := by nlinarith
  have hA0 : 0 < t + 3 * d * K - 1 / 2 := by nlinarith
  have s1 := F_tangent (y := t + (480 * K - 3 * d * K) + 1 / 2) (y₀ := t + (480 * K - 3 * d * K))
    (by linarith) hB0
  have s2 := F_tangent (y := t + 3 * d * K) (y₀ := t + 3 * d * K - 1 / 2) (by linarith) hA0
  have l1 : Real.log (t / 2) ≤ Real.log (t + (480 * K - 3 * d * K)) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have l2 : Real.log (t / 2) ≤ Real.log (t + 3 * d * K - 1 / 2) :=
    Real.log_le_log (by linarith) (by nlinarith)
  rw [Real.log_div (by linarith) (by norm_num)] at l1 l2
  -- scaling
  have hx1 : t + (480 * K - 3 * d * K) = (480 * K : ℝ) * (t / (480 * K) + 1 - d / 160) := by
    field_simp; ring
  have hx2 : t + 3 * d * K = (480 * K : ℝ) * (t / (480 * K) + d / 160) := by
    field_simp; ring
  have hxpos : 0 ≤ t / (480 * K) := div_nonneg (by linarith) hnpos.le
  have f1 := F_scale (n := (480 * K : ℝ)) (y := t / (480 * K) + 1 - d / 160) hnpos (by
    have : (d : ℝ) / 160 ≤ 1 := by linarith
    linarith)
  have f2 := F_scale (n := (480 * K : ℝ)) (y := t / (480 * K) + d / 160) hnpos (by positivity)
  rw [← hx1] at f1
  rw [← hx2] at f2
  have e3 : (t + (480 * K - 3 * d * K) + 1 / 2 - (t + (480 * K - 3 * d * K))) = 1 / 2 := by ring
  have e4 : (t + 3 * d * K - (t + 3 * d * K - 1 / 2)) = 1 / 2 := by ring
  rw [e3] at s1
  rw [e4] at s2
  nlinarith

/-- The numerator run `Σ_{l=-(1+r)n-1}^{rn} log(t - l)`. -/
lemma num_run_le (K : ℕ) (hK : 1 ≤ K) (t : ℝ) (ht : 560 * (K : ℝ) + 1 ≤ t) :
    ∑ l ∈ Icc (-(1040 * (K : ℤ)) - 1) (560 * (K : ℤ)), Real.log (t - (l : ℝ)) ≤
      (480 * (K : ℝ)) * (F (t / (480 * K) + 13 / 6) - F (t / (480 * K) - 7 / 6)) +
        10 / 3 * (480 * (K : ℝ)) * (Real.log (480 * K) - 1) +
        2 * Real.log (t + 1040 * K + 2) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hnpos : (0 : ℝ) < 480 * K := by positivity
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = 1600 * K + 1 := ⟨_, rfl⟩
  have hIcc : (560 * (K : ℤ)) = (-(1040 * (K : ℤ)) - 1) + (j : ℤ) := by rw [hj]; push_cast; ring
  rw [hIcc]
  have hjr : (j : ℝ) = 1600 * K + 1 := by rw [hj]; push_cast; ring
  have c1 : (((-(1040 * (K : ℤ)) - 1 : ℤ)) : ℝ) = -(1040 * (K : ℝ)) - 1 := by push_cast; ring
  have c2 : ((((-(1040 * (K : ℤ)) - 1) + (j : ℤ) : ℤ)) : ℝ) = 560 * K := by
    push_cast; rw [hjr]; ring
  have hrun := sum_log_int_le t (-(1040 * (K : ℤ)) - 1) j (by rw [c2]; linarith)
  rw [c1, c2, hjr] at hrun
  have e1 : t - (-(1040 * (K : ℝ)) - 1) + 1 = t + 1040 * K + 2 := by ring
  rw [e1] at hrun
  have s1 := F_tangent (y := t + 1040 * K) (y₀ := t + 1040 * K + 2) (by nlinarith) (by nlinarith)
  have hx1 : t + 1040 * K = (480 * K : ℝ) * (t / (480 * K) + 13 / 6) := by field_simp; ring
  have hx2 : t - 560 * K = (480 * K : ℝ) * (t / (480 * K) - 7 / 6) := by field_simp; ring
  have hxr : 7 / 6 ≤ t / (480 * K) := by
    rw [le_div_iff₀ hnpos]; nlinarith
  have f1 := F_scale (n := (480 * K : ℝ)) (y := t / (480 * K) + 13 / 6) hnpos (by linarith)
  have f2 := F_scale (n := (480 * K : ℝ)) (y := t / (480 * K) - 7 / 6) hnpos (by linarith)
  rw [← hx1] at f1
  rw [← hx2] at f2
  have e2 : t + 1040 * K - (t + 1040 * K + 2) = -2 := by ring
  rw [e2] at s1
  nlinarith

end BetaIrr.I3.Size
