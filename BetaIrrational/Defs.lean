/-
Copyright (c) 2026. All rights reserved.

# Dirichlet's beta function at natural arguments

Formalises the notation of `PROOF_BETA.md` (preamble):
`β(s) = ∑_{m ≥ 0} (-1)^m / (2m+1)^s`.
Status: complete (no `sorry`).
-/
import Mathlib

namespace BetaIrr

open scoped BigOperators

/-- The terms of Dirichlet's beta series. -/
noncomputable def betaTerm (s : ℕ) (m : ℕ) : ℝ := (-1 : ℝ) ^ m / (2 * (m : ℝ) + 1) ^ s

/-- Dirichlet's beta function `β(s) = ∑' m, (-1)^m / (2m+1)^s` at a natural number `s`.
(Only `s ≥ 2` is used; there the series converges absolutely.) -/
noncomputable def dirichletBeta (s : ℕ) : ℝ := ∑' m : ℕ, betaTerm s m

lemma norm_betaTerm_le {s : ℕ} (hs : 2 ≤ s) (m : ℕ) :
    ‖betaTerm s m‖ ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
  have h1 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hle : ((m : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ) + 1) ^ s := by
    calc ((m : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ) + 1) ^ 2 := by
          gcongr
          have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
      _ ≤ (2 * (m : ℝ) + 1) ^ s := pow_le_pow_right₀ h1 hs
  rw [betaTerm, norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow,
    Real.norm_of_nonneg (by linarith)]
  exact one_div_le_one_div_of_le (by positivity) hle

lemma summable_betaTerm {s : ℕ} (hs : 2 ≤ s) : Summable (betaTerm s) := by
  have hsum : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  exact Summable.of_norm_bounded hsum (norm_betaTerm_le hs)

end BetaIrr
