/-
# The target statement

`OneOfBeta4To36`: at least one of β(4), β(6), …, β(36) is irrational.

Proved here: the reduction of the statement to the existence of small integer linear forms in the
β-values that are nonzero infinitely often (PROOF_BETA §7, the contradiction step). The forms
themselves are constructed and bounded in `FamilyI3.lean` and `I3/`.
Status: complete (no `sorry`).
-/
import BetaIrrational.Defs
import BetaIrrational.Criterion

namespace BetaIrr

open Filter Topology
open scoped BigOperators

/-- **The main statement.** At least one of `β(4), β(6), …, β(36)` is irrational, where
`dirichletBeta s = ∑' m, (-1)^m / (2m+1)^s` (`Defs.lean`). -/
def OneOfBeta4To36 : Prop := ∃ j ∈ Finset.Icc 2 18, Irrational (dirichletBeta (2 * j))

/-- Small integer linear forms `a n + ∑_{j=2}^{J} c n j β(2j)` that are nonzero infinitely
often prove that one of `β(4), …, β(2J)` is irrational. -/
theorem exists_irrational_beta_of_forms (J : ℕ) (a : ℕ → ℤ) (c : ℕ → ℕ → ℤ)
    (hlim : Tendsto
      (fun n => (a n : ℝ) + ∑ j ∈ Finset.Icc 2 J, (c n j : ℝ) * dirichletBeta (2 * j))
      atTop (𝓝 0))
    (hne : ∃ᶠ n in atTop,
      (a n : ℝ) + ∑ j ∈ Finset.Icc 2 J, (c n j : ℝ) * dirichletBeta (2 * j) ≠ 0) :
    ∃ j ∈ Finset.Icc 2 J, Irrational (dirichletBeta (2 * j)) :=
  exists_irrational_of_small_forms (Finset.Icc 2 J) (fun j => dirichletBeta (2 * j)) a c hlim hne

theorem oneOfBeta4To36_of_forms (a : ℕ → ℤ) (c : ℕ → ℕ → ℤ)
    (hlim : Tendsto
      (fun n => (a n : ℝ) + ∑ j ∈ Finset.Icc 2 18, (c n j : ℝ) * dirichletBeta (2 * j))
      atTop (𝓝 0))
    (hne : ∃ᶠ n in atTop,
      (a n : ℝ) + ∑ j ∈ Finset.Icc 2 18, (c n j : ℝ) * dirichletBeta (2 * j) ≠ 0) :
    OneOfBeta4To36 :=
  exists_irrational_beta_of_forms 18 a c hlim hne

end BetaIrr
