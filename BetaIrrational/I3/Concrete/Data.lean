/-
# Instance I3: the concrete partial-fraction data

The partial-fraction data of `R_n` (`FamilyI3.lean`). PROOF_BETA §3 local formula. With
`t₀ = -k - 1/2` and `f_k(t) = R_n(t) (t + k + 1/2)^{B_k}`:
`a_{i,k} = [ε^{B_k - i}] f_k(t₀ + ε)`, where

`f_k(t₀+ε) = (u_e + 2ε) · Π_l (u_l + ε)^3 · Π_{j} Π_{k' ∈ block j, k' ≠ k} (d_{k'} + ε)^{-1}`,

* `u_l = -k - 1/2 - l` for the integer zeros `l ∈ [-1040(m+1)-1, 560(m+1)]` (multiplicity 3);
* `u_e = n - 2k` (the e-factor `2t + n + 1`, `e = 1`);
* `d_{k'} = k' - k` (one factor per block containing `k'`).

This file only *defines* things (`Bk`, `numSeries`, `denSeries`, `fSeries`, `a`, `pf`).

Status: complete (definitions only, no `sorry`).
-/
import BetaIrrational.Expansion
import BetaIrrational.FamilyI3
import Mathlib.RingTheory.PowerSeries.Inverse

namespace BetaIrr.I3

open Finset PowerSeries
open scoped BigOperators

/-- Block membership count `B_k = Σ_j m_j [δ_j n ≤ k ≤ (1-δ_j) n]`. -/
def Bk (m k : ℕ) : ℕ :=
  (blocks.map (fun b => if 3 * b.1 * (m + 1) ≤ k ∧ k ≤ nOf m - 3 * b.1 * (m + 1) then b.2 else 0)).sum

/-- The numerator part of `f_k(t₀ + X)` as a polynomial-valued power series over ℚ. -/
noncomputable def numSeries (m k : ℕ) : PowerSeries ℚ :=
  (C ((nOf m : ℚ) - 2 * k) + 2 * X) *
    ∏ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)),
      (C (-(k : ℚ) - 1 / 2 - l) + X) ^ 3

/-- The pole part: `Π_j Π_{k' ∈ block j, k' ≠ k} (k' - k + X)^{-1}`. -/
noncomputable def denSeries (m k : ℕ) : PowerSeries ℚ :=
  (blocks.map (fun b =>
    (∏ k' ∈ (Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1))).erase k,
      (C ((k' : ℚ) - k) + X)⁻¹) ^ b.2)).prod

/-- `f_k(t₀ + X)` as a power series over ℚ. -/
noncomputable def fSeries (m k : ℕ) : PowerSeries ℚ := numSeries m k * denSeries m k

/-- `a_{i,k} = [X^{B_k - i}] f_k(t₀ + X)` for `1 ≤ i ≤ B_k`, else `0`. -/
noncomputable def a (m i k : ℕ) : ℚ :=
  if 1 ≤ i ∧ i ≤ Bk m k then coeff (Bk m k - i) (fSeries m k) else 0

/-- The partial-fraction data of `R_n` (`I = S = 35`, `K = n`). -/
noncomputable def pf (m : ℕ) : PFData where
  I := 35
  K := nOf m
  a := a m

end BetaIrr.I3
