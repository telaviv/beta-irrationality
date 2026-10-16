/-
# `F_n = P_n H_n / π²` in the upper half plane (PROOF_BETA100 (6.2.1))

With `G_i(z) = s_i z + n u_i + β_i`, `P_n(z) = (2z + n + 1) Π Γ(G_i(z))^{c_i}` (`Gamma.lean`),

    μ(z)  = 2/(2z + n + 1) + Σ c_i s_i ψ(G_i(z))           (= P_n'/P_n),
    μ'(z) = -4/(2z + n + 1)² + Σ c_i s_i² ψ'(G_i(z)),
    H_n(z) = sin²(πz)(μ² + μ') + 6π μ sin(πz) cos(πz) + 3π² (2cos²(πz) - sin²(πz)),

and for `Im z > 0`: `F_n(z) = R_n''(z) π/sin(πz) = P_n(z) H_n(z)/π²` (`Fn_eq_PH`).

58 factors; the instance-independent lemmas
(`hasDerivAt_prod_logDeriv`, `S0`, `S1`, `S2`, …) are in `Fam/Analytic/Helpers.lean`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.ContourI3

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real Finset Filter Topology
open BetaIrr.Analytic BetaIrr.Fam.Analytic


/-- `G_i(z) = s_i z + n u_i + β_i`. -/
noncomputable def Gi (m : ℕ) (i : Fin 58) (z : ℂ) : ℂ :=
  sI i * z + (I3.nOf m : ℂ) * uI i + βI i

lemma Gi_im (m : ℕ) (i : Fin 58) (z : ℂ) : (Gi m i z).im = sI i * z.im := by
  simp [Gi]

lemma sI_ne_zero (i : Fin 58) : sI i ≠ 0 := by
  intro h; have := sI_sq i; rw [h] at this; norm_num at this

lemma Gi_im_ne (m : ℕ) (i : Fin 58) {z : ℂ} (hz : z.im ≠ 0) : (Gi m i z).im ≠ 0 := by
  rw [Gi_im]; exact mul_ne_zero (sI_ne_zero i) hz

lemma hasDerivAt_Gi (m : ℕ) (i : Fin 58) (z : ℂ) : HasDerivAt (Gi m i) (sI i) z := by
  have := ((hasDerivAt_id z).const_mul (sI i : ℂ)).add_const ((I3.nOf m : ℂ) * uI i + βI i)
  have hfun : Gi m i = fun w => (sI i : ℂ) * id w + ((I3.nOf m : ℂ) * uI i + βI i) := by
    funext w; simp [Gi, add_assoc]
  rw [hfun]
  convert this using 1
  simp

/-- `μ`. -/
noncomputable def muI (m : ℕ) (z : ℂ) : ℂ :=
  2 / (2 * z + (I3.nOf m : ℂ) + 1) +
    ∑ i, (cI i : ℂ) * sI i * Complex.digamma (Gi m i z)

/-- `μ'`. -/
noncomputable def mu1I (m : ℕ) (z : ℂ) : ℂ :=
  -4 / (2 * z + (I3.nOf m : ℂ) + 1) ^ 2 +
    ∑ i, (cI i : ℂ) * sI i ^ 2 * deriv Complex.digamma (Gi m i z)

lemma lin_ne_zero (m : ℕ) {z : ℂ} (hz : z.im ≠ 0) : 2 * z + (I3.nOf m : ℂ) + 1 ≠ 0 := by
  intro h; apply hz
  have := congrArg Complex.im h
  simp at this
  linarith

/-- `P_n' = P_n μ` where `Im z ≠ 0`. -/
lemma hasDerivAt_Pfun (m : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (Pfun m) (Pfun m z * muI m z) z := by
  have hfac : ∀ i ∈ (univ : Finset (Fin 58)), HasDerivAt
      (fun w => Complex.Gamma (Gi m i w) ^ cI i)
      (Complex.Gamma (Gi m i z) ^ cI i * ((cI i : ℂ) * sI i * Complex.digamma (Gi m i z))) z := by
    intro i _
    have hw := ne_neg_nat_of_im (Gi_im_ne m i hz)
    have hG := Complex.Gamma_ne_zero hw
    have h1 := (hasDerivAt_Gamma_digamma hw).comp z (hasDerivAt_Gi m i z)
    have h2 := (hasDerivAt_zpow (cI i) _ (Or.inl hG)).comp z h1
    refine h2.congr_deriv ?_
    rw [zpow_sub_one₀ hG]
    field_simp
  have hprod := hasDerivAt_prod_logDeriv univ (fun i w => Complex.Gamma (Gi m i w) ^ cI i)
    (fun i => (cI i : ℂ) * sI i * Complex.digamma (Gi m i z)) hfac
  have hlin : HasDerivAt (fun w : ℂ => 2 * w + (I3.nOf m : ℂ) + 1) 2 z := by
    have := ((hasDerivAt_id z).const_mul (2 : ℂ)).add_const ((I3.nOf m : ℂ) + 1)
    convert this using 1
    · funext w; simp; ring
    · simp
  have h := hlin.mul hprod
  have hP : Pfun m = fun w => (2 * w + (I3.nOf m : ℂ) + 1) *
      ∏ i, Complex.Gamma (Gi m i w) ^ cI i := by
    funext w; rfl
  rw [hP]
  convert h using 1
  have hne := lin_ne_zero m hz
  unfold muI
  field_simp

/-- `μ' = mu1I`. -/
lemma hasDerivAt_muI (m : ℕ) {z : ℂ} (hz : z.im ≠ 0) : HasDerivAt (muI m) (mu1I m z) z := by
  have hne := lin_ne_zero m hz
  have hlin : HasDerivAt (fun w : ℂ => 2 * w + (I3.nOf m : ℂ) + 1) 2 z := by
    have := ((hasDerivAt_id z).const_mul (2 : ℂ)).add_const ((I3.nOf m : ℂ) + 1)
    convert this using 1
    · funext w; simp; ring
    · simp
  have h1 : HasDerivAt (fun w : ℂ => 2 / (2 * w + (I3.nOf m : ℂ) + 1))
      (-4 / (2 * z + (I3.nOf m : ℂ) + 1) ^ 2) z := by
    have := (hlin.inv hne).const_mul (2 : ℂ)
    convert this using 1
    · funext w; simp [div_eq_mul_inv]
    · ring
  have h2 : ∀ i ∈ (univ : Finset (Fin 58)), HasDerivAt
      (fun w => (cI i : ℂ) * sI i * Complex.digamma (Gi m i w))
      ((cI i : ℂ) * sI i ^ 2 * deriv Complex.digamma (Gi m i z)) z := by
    intro i _
    have hw : Gi m i z ∈ slitPlane := mem_slitPlane_of_im (Gi_im_ne m i hz)
    have hd := ((Stirling.hasDerivAt_digamma hw).differentiableAt.hasDerivAt).comp z
      (hasDerivAt_Gi m i z)
    exact (hd.const_mul ((cI i : ℂ) * sI i)).congr_deriv (by ring)
  have h3 := HasDerivAt.fun_sum h2
  have := h1.add h3
  unfold muI mu1I
  exact this

/-- `R_n = P_n S` in the upper half plane. -/
lemma RC_eq_PS (m : ℕ) {z : ℂ} (hz : z.im ≠ 0) : RC m z = Pfun m z * S0 z := by
  rw [RC_eq_Pfun m z hz, S0]; ring

/-- **`R_n'' = P_n ((μ² + μ') S + 2μ S' + S'')`** in the upper half plane. -/
theorem fC_eq (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    fC m z = Pfun m z * ((muI m z ^ 2 + mu1I m z) * S0 z + 2 * muI m z * S1 z + S2 z) := by
  have hH : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hd1 : ∀ w : ℂ, 0 < w.im → deriv (RC m) w = Pfun m w * (muI m w * S0 w + S1 w) := by
    intro w hw
    have heq : RC m =ᶠ[𝓝 w] fun v => Pfun m v * S0 v := by
      filter_upwards [hH.mem_nhds hw] with v hv using RC_eq_PS m (ne_of_gt hv)
    rw [heq.deriv_eq, ((hasDerivAt_Pfun m (ne_of_gt hw)).fun_mul (hasDerivAt_S0 w)).deriv]
    ring
  have heq : deriv (RC m) =ᶠ[𝓝 z] fun v => Pfun m v * (muI m v * S0 v + S1 v) := by
    filter_upwards [hH.mem_nhds hz] with v hv using hd1 v hv
  unfold fC
  rw [heq.deriv_eq]
  have h := (hasDerivAt_Pfun m (ne_of_gt hz)).fun_mul
    (((hasDerivAt_muI m (ne_of_gt hz)).fun_mul (hasDerivAt_S0 z)).fun_add (hasDerivAt_S1 z))
  rw [h.deriv]
  ring

/-- `H_n`. -/
noncomputable def Hn (m : ℕ) (z : ℂ) : ℂ :=
  Complex.sin (π * z) ^ 2 * (muI m z ^ 2 + mu1I m z)
    + 6 * π * muI m z * Complex.sin (π * z) * Complex.cos (π * z)
    + 3 * π ^ 2 * (2 * Complex.cos (π * z) ^ 2 - Complex.sin (π * z) ^ 2)

/-- **(6.2.1)** `F_n = P_n H_n / π²` for `Im z > 0`. -/
theorem Fn_eq_PH (m : ℕ) {z : ℂ} (hz : 0 < z.im) : Fn m z = Pfun m z * Hn m z / π ^ 2 := by
  have hs := sin_pi_ne_zero_of_im (ne_of_gt hz)
  unfold Fn Fker cscPi
  rw [fC_eq m hz]
  unfold S0 S1 S2 Hn
  have := hπC
  field_simp
  ring

end BetaIrr.I3.Analytic
