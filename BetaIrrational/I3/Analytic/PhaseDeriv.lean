/-
# Derivatives of the phase `f = Ψ - 2πix` and holomorphy of the amplitude `A`

In the upper half plane every `α_i(x) = s_i x + u_i` lies in the slit plane, and

    Ψ' = Σ c_i s_i log α_i,   Ψ'' = Σ c_i s_i²/α_i,   Ψ''' = -Σ c_i s_i³/α_i²

(`hasDerivAt_PsiI`, `hasDerivAt_Psi1I`, `hasDerivAt_Psi2I`; the first uses `Σ c_i s_i = 0`).
`Alim` (the limiting amplitude) is holomorphic there (`differentiableAt_Alim`).

Mirrors `Analytic/PhaseDeriv.lean` (instance I3).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.FnPath

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real Finset Filter Topology
open BetaIrr.Analytic BetaIrr.Fam.Analytic


lemma alphaI_im (i : Fin 58) (x : ℂ) : (alphaI i x).im = sI i * x.im := by
  simp [alphaI]

lemma alphaI_slit (i : Fin 58) {x : ℂ} (hx : x.im ≠ 0) : alphaI i x ∈ slitPlane :=
  Or.inr (by rw [alphaI_im]; exact mul_ne_zero (sI_ne_zero i) hx)

lemma alphaI_ne_zero (i : Fin 58) {x : ℂ} (hx : x.im ≠ 0) : alphaI i x ≠ 0 :=
  slitPlane_ne_zero (alphaI_slit i hx)

lemma hasDerivAt_alphaI (i : Fin 58) (x : ℂ) : HasDerivAt (alphaI i) (sI i) x := by
  have := ((hasDerivAt_id x).const_mul (sI i : ℂ)).add_const (uI i : ℂ)
  have hf : alphaI i = fun y => (sI i : ℂ) * id y + (uI i : ℂ) := by funext y; simp [alphaI]
  rw [hf]
  exact this.congr_deriv (by simp)

lemma hasDerivAt_PsiI {x : ℂ} (hx : x.im ≠ 0) : HasDerivAt PsiI (Psi1I x) x := by
  have h : ∀ i ∈ (univ : Finset (Fin 58)), HasDerivAt
      (fun y => (cI i : ℂ) * (alphaI i y * Complex.log (alphaI i y)))
      ((cI i : ℂ) * (sI i * Complex.log (alphaI i x) + sI i)) x := by
    intro i _
    have hα := hasDerivAt_alphaI i x
    have hl := hα.clog (alphaI_slit i hx)
    have := (hα.mul hl).const_mul (cI i : ℂ)
    refine this.congr_deriv ?_
    have hne := alphaI_ne_zero i hx
    field_simp
  have hs := HasDerivAt.fun_sum h
  unfold PsiI
  refine hs.congr_deriv ?_
  unfold Psi1I
  rw [← sub_eq_zero, ← sum_sub_distrib]
  have : ∑ i, ((cI i : ℂ) * (sI i * Complex.log (alphaI i x) + sI i)
      - (cI i : ℂ) * sI i * Complex.log (alphaI i x)) = ∑ i, (cI i : ℂ) * sI i :=
    sum_congr rfl (fun i _ => by ring)
  rw [this, sum_cs_C]

lemma hasDerivAt_Psi1I {x : ℂ} (hx : x.im ≠ 0) : HasDerivAt Psi1I (Psi2I x) x := by
  have h : ∀ i ∈ (univ : Finset (Fin 58)), HasDerivAt
      (fun y => (cI i : ℂ) * sI i * Complex.log (alphaI i y))
      ((cI i : ℂ) * sI i ^ 2 / alphaI i x) x := by
    intro i _
    have hl := (hasDerivAt_alphaI i x).clog (alphaI_slit i hx)
    have := hl.const_mul ((cI i : ℂ) * sI i)
    refine this.congr_deriv ?_
    have hne := alphaI_ne_zero i hx
    field_simp
  exact HasDerivAt.fun_sum h

lemma hasDerivAt_Psi2I {x : ℂ} (hx : x.im ≠ 0) : HasDerivAt Psi2I (Psi3I x) x := by
  have h : ∀ i ∈ (univ : Finset (Fin 58)), HasDerivAt
      (fun y => (cI i : ℂ) * sI i ^ 2 / alphaI i y)
      (-((cI i : ℂ) * sI i ^ 3 / alphaI i x ^ 2)) x := by
    intro i _
    have hne := alphaI_ne_zero i hx
    have := ((hasDerivAt_alphaI i x).inv hne).const_mul ((cI i : ℂ) * sI i ^ 2)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · field_simp
    · exact Eventually.of_forall (fun y => by simp [div_eq_mul_inv])
  have hs := HasDerivAt.fun_sum h
  unfold Psi2I
  refine hs.congr_deriv ?_
  unfold Psi3I
  rw [sum_neg_distrib]

lemma hasDerivAt_phaseI {x : ℂ} (hx : x.im ≠ 0) :
    HasDerivAt phaseI (Psi1I x - 2 * π * I) x := by
  have := (hasDerivAt_PsiI hx).fun_sub ((hasDerivAt_id x).const_mul (2 * π * I : ℂ))
  have hf : phaseI = fun y => PsiI y - 2 * π * I * id y := by funext y; simp [phaseI]
  rw [hf]
  exact this.congr_deriv (by simp)

lemma differentiableAt_psi0I {x : ℂ} (hx : x.im ≠ 0) : DifferentiableAt ℂ psi0I x := by
  unfold psi0I
  refine DifferentiableAt.fun_sum (fun i _ => ?_)
  exact ((hasDerivAt_alphaI i x).clog (alphaI_slit i hx)).differentiableAt.const_mul _

lemma differentiableAt_Alim {x : ℂ} (hx : x.im ≠ 0) : DifferentiableAt ℂ Alim x := by
  have h1 := differentiableAt_psi0I hx
  have h2 := (hasDerivAt_Psi1I hx).differentiableAt
  have h3 : DifferentiableAt ℂ (fun y : ℂ => 2 * y + 1) x := by fun_prop
  unfold Alim
  have := ((h3.mul h1.cexp).mul (((h2.sub_const (3 * π * I : ℂ)).pow 2).neg.div_const 4)).div_const
    ((π : ℂ) ^ 2)
  exact this

lemma differentiableOn_Alim : DifferentiableOn ℂ Alim {x : ℂ | 0 < x.im} :=
  fun x hx => (differentiableAt_Alim (ne_of_gt hx)).differentiableWithinAt

lemma continuousOn_phaseI : ContinuousOn phaseI {x : ℂ | 0 < x.im} :=
  fun x hx => (hasDerivAt_phaseI (ne_of_gt hx)).continuousAt.continuousWithinAt

end BetaIrr.I3.Analytic
