/-
# The I3 factor list and phase, list form (PROOF_BETA §6.2, instance I3)

Instance I3: `μ_in = 3`, `r = 7/6`, `q = 480`; factor list (`c, s, κ` with `α = s x + κ`)

    (3, x + 1 + r), (3, r - x), and for each block (k, m), δ = k/160:  (m, x + δ), (-m, x + 1 - δ),

blocks `(0, 8)` and `(k, 1)` for `k = 1…8, 10, 12, …, 46` (`BetaIrr.I3.blocks`); 58 factors, in the
order of `I3/Analytic/Factors.lean` (`facI3_eq_blocks`).

Definitions (principal `Complex.log`): `Ψ = psiL facI3`, `f z = Ψ z - 2πi z`, `g z = Ψ'(z) - 2πi`,
with the derivative chain `f → g → Ψ'' → Ψ'''` on `Im z ≠ 0`.

This file has no expensive kernel checks; every other file of the I3 certificate imports it.

Status: complete (no `sorry`).
-/
import BetaIrrational.Interval.Psi
import BetaIrrational.Interval.Segment
import BetaIrrational.FamilyI3

namespace BetaIrr.I3.Interval

open Complex BetaIrr.Interval Real

/-- Factor list of instance I3 (`c, s, κ` with `α = s x + κ`). -/
def facI3 : List Fac :=
  [⟨3, 1, 13 / 6⟩, ⟨3, -1, 7 / 6⟩, ⟨8, 1, 0⟩, ⟨-8, 1, 1⟩,
   ⟨1, 1, 1 / 160⟩, ⟨-1, 1, 159 / 160⟩, ⟨1, 1, 2 / 160⟩, ⟨-1, 1, 158 / 160⟩,
   ⟨1, 1, 3 / 160⟩, ⟨-1, 1, 157 / 160⟩, ⟨1, 1, 4 / 160⟩, ⟨-1, 1, 156 / 160⟩,
   ⟨1, 1, 5 / 160⟩, ⟨-1, 1, 155 / 160⟩, ⟨1, 1, 6 / 160⟩, ⟨-1, 1, 154 / 160⟩,
   ⟨1, 1, 7 / 160⟩, ⟨-1, 1, 153 / 160⟩, ⟨1, 1, 8 / 160⟩, ⟨-1, 1, 152 / 160⟩,
   ⟨1, 1, 10 / 160⟩, ⟨-1, 1, 150 / 160⟩, ⟨1, 1, 12 / 160⟩, ⟨-1, 1, 148 / 160⟩,
   ⟨1, 1, 14 / 160⟩, ⟨-1, 1, 146 / 160⟩, ⟨1, 1, 16 / 160⟩, ⟨-1, 1, 144 / 160⟩,
   ⟨1, 1, 18 / 160⟩, ⟨-1, 1, 142 / 160⟩, ⟨1, 1, 20 / 160⟩, ⟨-1, 1, 140 / 160⟩,
   ⟨1, 1, 22 / 160⟩, ⟨-1, 1, 138 / 160⟩, ⟨1, 1, 24 / 160⟩, ⟨-1, 1, 136 / 160⟩,
   ⟨1, 1, 26 / 160⟩, ⟨-1, 1, 134 / 160⟩, ⟨1, 1, 28 / 160⟩, ⟨-1, 1, 132 / 160⟩,
   ⟨1, 1, 30 / 160⟩, ⟨-1, 1, 130 / 160⟩, ⟨1, 1, 32 / 160⟩, ⟨-1, 1, 128 / 160⟩,
   ⟨1, 1, 34 / 160⟩, ⟨-1, 1, 126 / 160⟩, ⟨1, 1, 36 / 160⟩, ⟨-1, 1, 124 / 160⟩,
   ⟨1, 1, 38 / 160⟩, ⟨-1, 1, 122 / 160⟩, ⟨1, 1, 40 / 160⟩, ⟨-1, 1, 120 / 160⟩,
   ⟨1, 1, 42 / 160⟩, ⟨-1, 1, 118 / 160⟩, ⟨1, 1, 44 / 160⟩, ⟨-1, 1, 116 / 160⟩,
   ⟨1, 1, 46 / 160⟩, ⟨-1, 1, 114 / 160⟩]

/-- The factor list is built from the I3 blocks `(k, m)` exactly as in PROOF_BETA §6.2
(`μ_in = 3`, `r = 7/6`, `δ = k/160`). -/
lemma facI3_eq_blocks :
    facI3 = [⟨3, 1, 1 + 7 / 6⟩, ⟨3, -1, 7 / 6⟩] ++
      (BetaIrr.I3.blocks.flatMap fun b =>
        [⟨(b.2 : ℤ), 1, (b.1 : ℚ) / 160⟩, ⟨-(b.2 : ℤ), 1, 1 - (b.1 : ℚ) / 160⟩]) := by
  decide +kernel

lemma facI3_length : facI3.length = 58 := by decide

lemma facI3_s : ∀ a ∈ facI3, a.s ≠ 0 := by decide

lemma facI3_s1 : ∀ a ∈ facI3, a.s = 1 ∨ a.s = -1 := by decide

/-! ## Analytic objects -/

/-- `Ψ(z) = Σ c_i α_i(z) log α_i(z)`. -/
noncomputable def Ψ : ℂ → ℂ := psiL facI3

/-- `f(z) = Ψ(z) - 2πi z`. -/
noncomputable def f (z : ℂ) : ℂ := Ψ z - 2 * π * I * z

/-- `g(z) = Ψ'(z) - 2πi`. -/
noncomputable def g (z : ℂ) : ℂ := dpsiL facI3 z - 2 * π * I

lemma f_eq_fL : f = fL facI3 := rfl

lemma good_of_im {z : ℂ} (hz : z.im ≠ 0) : Good facI3 z := good_of_im_ne_zero facI3_s hz

lemma I3_hasDerivAt_Ψ {z : ℂ} (hz : z.im ≠ 0) : HasDerivAt Ψ (dpsiL facI3 z) z :=
  hasDerivAt_psiL facI3 (good_of_im hz)

lemma I3_hasDerivAt_f {z : ℂ} (hz : z.im ≠ 0) : HasDerivAt f (g z) z := by
  have := (I3_hasDerivAt_Ψ hz).sub ((hasDerivAt_id z).const_mul (2 * π * I))
  rw [mul_one] at this
  exact this

lemma I3_hasDerivAt_g {z : ℂ} (hz : z.im ≠ 0) : HasDerivAt g (d2psiL facI3 z) z :=
  (hasDerivAt_dpsiL facI3 (good_of_im hz)).sub_const (2 * π * I)

lemma I3_hasDerivAt_d2 {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (d2psiL facI3) (d3psiL facI3 z) z :=
  hasDerivAt_d2psiL facI3 (good_of_im hz)

lemma deriv_Ψ {z : ℂ} (hz : z.im ≠ 0) : deriv Ψ z = dpsiL facI3 z := (I3_hasDerivAt_Ψ hz).deriv

end BetaIrr.I3.Interval
