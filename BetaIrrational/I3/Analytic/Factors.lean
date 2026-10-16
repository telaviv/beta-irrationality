/-
# The I3 factor list and the phase (PROOF_BETA §6.2, instance I3: `μ_in = 3`, `r = 7/6`)

Fifty-eight Γ-factors `(c_i, s_i, u_i, β_i)`, `α_i(x) = s_i x + u_i`:
* `i = 0`: `(3, +1, 13/6, 2)` (`Γ(z + (1+r)n + 2)³`); `i = 1`: `(3, -1, 7/6, 1)` (`Γ(rn + 1 - z)³`);
* block `j = 0..27` with `(k_j, m_j)` from `I3.blocks` (`δ_j = k_j/160`):
  `i = 2 + 2j`: `(m_j, +1, k_j/160, 1/2)`, `i = 3 + 2j`: `(-m_j, +1, 1 - k_j/160, 3/2)`.

Identities: `Σ c_i s_i = 0`, `Σ c_i u_i = -G = -179/10`, `Σ c_i (β_i - 1/2) = -29`, `Σ c_i = 6`,
`Σ |c_i| = 76`, `Σ |c_i (β_i - 1/2)| = 41`.

Phase functions (mirroring `Analytic/PathAsymp.lean`): `alphaI`, `PsiI = Σ c_i α_i log α_i`,
`Psi1I = Σ c_i s_i log α_i`, `Psi2I = Σ c_i s_i²/α_i`, `Psi3I = -Σ c_i s_i³/α_i²`,
`psi0I = Σ c_i (β_i - 1/2) log α_i`, `phaseI = PsiI - 2πi x`, `lamN`, `SectorAt`.

It imports only Mathlib.

Status: complete (no `sorry`).
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real Finset

/-- `c_i`. -/
def cI : Fin 58 → ℤ :=
  ![3, 3, 8, -8, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1]

/-- `s_i`. -/
def sI : Fin 58 → ℝ :=
  ![1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- `u_i`. -/
noncomputable def uI : Fin 58 → ℝ :=
  ![13 / 6, 7 / 6, 0, 1, 1 / 160, 159 / 160, 2 / 160, 158 / 160, 3 / 160, 157 / 160,
    4 / 160, 156 / 160, 5 / 160, 155 / 160, 6 / 160, 154 / 160, 7 / 160, 153 / 160,
    8 / 160, 152 / 160, 10 / 160, 150 / 160, 12 / 160, 148 / 160, 14 / 160, 146 / 160,
    16 / 160, 144 / 160, 18 / 160, 142 / 160, 20 / 160, 140 / 160, 22 / 160, 138 / 160,
    24 / 160, 136 / 160, 26 / 160, 134 / 160, 28 / 160, 132 / 160, 30 / 160, 130 / 160,
    32 / 160, 128 / 160, 34 / 160, 126 / 160, 36 / 160, 124 / 160, 38 / 160, 122 / 160,
    40 / 160, 120 / 160, 42 / 160, 118 / 160, 44 / 160, 116 / 160, 46 / 160, 114 / 160]

/-- `β_i`. -/
noncomputable def βI : Fin 58 → ℝ :=
  ![2, 1, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2,
    1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2,
    1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2,
    1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2,
    1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2, 1 / 2, 3 / 2]

lemma sum_cs : ∑ i, (cI i : ℝ) * sI i = 0 := by
  norm_num [Fin.sum_univ_succ, cI, sI]

lemma sum_cu : ∑ i, (cI i : ℝ) * uI i = -(179 / 10) := by
  norm_num [Fin.sum_univ_succ, cI, uI]

lemma sum_cβ : ∑ i, (cI i : ℝ) * (βI i - 1 / 2) = -29 := by
  norm_num [Fin.sum_univ_succ, cI, βI]

lemma sum_c : ∑ i, (cI i : ℝ) = 6 := by
  norm_num [Fin.sum_univ_succ, cI]

lemma sum_abs_c : ∑ i, |(cI i : ℝ)| = 76 := by
  norm_num [Fin.sum_univ_succ, cI]

lemma sum_abs_cs : ∑ i, |(cI i : ℝ) * sI i| = 76 := by
  norm_num [Fin.sum_univ_succ, cI, sI]

lemma sum_abs_cs2 : ∑ i, |(cI i : ℝ) * sI i ^ 2| = 76 := by
  norm_num [Fin.sum_univ_succ, cI, sI]

lemma sum_abs_cβ : ∑ i, |(cI i : ℝ) * (βI i - 1 / 2)| = 41 := by
  norm_num [Fin.sum_univ_succ, cI, βI]

lemma sI_sq (i : Fin 58) : sI i ^ 2 = 1 := by
  fin_cases i <;> simp [sI]

lemma βI_pos (i : Fin 58) : 0 < βI i ∧ βI i ≤ 2 := by
  fin_cases i <;> simp [βI] <;> norm_num

lemma uI_bound (i : Fin 58) : |uI i| ≤ 3 := by
  fin_cases i <;> simp [uI] <;> norm_num [abs_of_nonneg]

/-- `α_i(x) = s_i x + u_i`. -/
noncomputable def alphaI (i : Fin 58) (x : ℂ) : ℂ := sI i * x + uI i

/-- `Ψ(x) = Σ c_i α_i log α_i`. -/
noncomputable def PsiI (x : ℂ) : ℂ := ∑ i, (cI i : ℂ) * (alphaI i x * Complex.log (alphaI i x))

/-- `Ψ'(x) = Σ c_i s_i log α_i`. -/
noncomputable def Psi1I (x : ℂ) : ℂ := ∑ i, (cI i : ℂ) * sI i * Complex.log (alphaI i x)

/-- `Ψ''(x) = Σ c_i s_i² / α_i`. -/
noncomputable def Psi2I (x : ℂ) : ℂ := ∑ i, (cI i : ℂ) * sI i ^ 2 / alphaI i x

/-- `Ψ'''(x) = -Σ c_i s_i³ / α_i²`. -/
noncomputable def Psi3I (x : ℂ) : ℂ := -∑ i, (cI i : ℂ) * sI i ^ 3 / alphaI i x ^ 2

/-- `ψ₀(x) = Σ c_i (β_i - 1/2) log α_i`. -/
noncomputable def psi0I (x : ℂ) : ℂ := ∑ i, (cI i : ℂ) * (βI i - 1 / 2) * Complex.log (alphaI i x)

/-- The phase `f(x) = Ψ(x) - 2πi x`. -/
noncomputable def phaseI (x : ℂ) : ℂ := PsiI x - 2 * π * I * x

/-- `λ_n = -G n log n + G n - 29 log n + 3 log 2π` (`G = 179/10`). -/
noncomputable def lamN (n : ℝ) : ℝ :=
  -(179 / 10) * n * Real.log n + (179 / 10) * n - 29 * Real.log n + 3 * Real.log (2 * π)

/-- The sector condition (S4) at `x`. -/
def SectorAt (a η : ℝ) (x : ℂ) : Prop :=
  ∀ i, a ≤ ‖alphaI i x‖ ∧ |Complex.arg (alphaI i x)| ≤ π - η

end BetaIrr.I3.Analytic
