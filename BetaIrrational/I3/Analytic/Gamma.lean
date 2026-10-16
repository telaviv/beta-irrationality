/-
# Γ-factorisation of `R_n` for instance I3 (PROOF_BETA §6.2)

The complex extension `RC m` of `I3.R m` (`RC_ofReal`), the Γ-product `En m` (the `E_n` of §6.2,
with `p = 1040(m+1) + 1`, `q = 560(m+1)`), and

    RC m z = (2z + n + 1) · E_n(z) · sin³(πz) / π³        (`RC_eq_En`)

for `z` neither an integer nor a half-integer (`(-1)^{3q} = 1` since `q` is even). In factor-list
form (`Factors.lean`): `RC m z = P_n(z) sin³(πz)/π³` with
`P_n(z) = (2z + n + 1) Π_i Γ(s_i z + n u_i + β_i)^{c_i}` (`RC_eq_Pfun`).

Status: complete (no `sorry`).
-/
import BetaIrrational.FamilyI3
import BetaIrrational.I3.Analytic.Factors
import BetaIrrational.Fam.Analytic.Helpers

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real Finset
open BetaIrr.Fam.Analytic

/-- The complex extension of `I3.R m`. -/
noncomputable def RC (m : ℕ) (z : ℂ) : ℂ :=
  (2 * z + (I3.nOf m : ℂ) + 1) *
    (∏ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)), (z - (l : ℂ)) ^ 3) /
    (I3.blocks.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (I3.nOf m - 3 * b.1 * (m + 1)),
        (z + (k : ℂ) + 1 / 2)) ^ b.2)).prod

/-- `RC m` extends `I3.R m`. -/
lemma RC_ofReal (m : ℕ) (t : ℝ) : RC m t = (I3.R m t : ℂ) := by
  unfold RC I3.R
  rw [Complex.ofReal_div, Complex.ofReal_mul, list_prod_map_ofReal]
  push_cast
  rfl

/-- The Γ-product `E_n(z)` of PROOF_BETA §6.2 for I3 (`p = 1040(m+1)+1`, `q = 560(m+1)`). -/
noncomputable def En (m : ℕ) (z : ℂ) : ℂ :=
  Complex.Gamma (z + (1040 * (m + 1) + 1 : ℕ) + 1) ^ 3 *
    Complex.Gamma ((560 * (m + 1) : ℕ) + 1 - z) ^ 3 *
    (I3.blocks.map (fun b =>
      (Complex.Gamma (z + (3 * b.1 * (m + 1) : ℕ) + 1 / 2) /
        Complex.Gamma (z + (I3.nOf m - 3 * b.1 * (m + 1) : ℕ) + 3 / 2)) ^ b.2)).prod

/-- **Γ-factorisation for I3.** For `z` not an integer and not a half-integer,
`RC m z = (2z + n + 1) E_n(z) sin³(πz)/π³`. -/
theorem RC_eq_En (m : ℕ) (z : ℂ) (hz : ∀ k : ℤ, z ≠ k) (hz' : ∀ k : ℤ, z ≠ k + 1 / 2) :
    RC m z = (2 * z + (I3.nOf m : ℂ) + 1) * En m z * Complex.sin (π * z) ^ 3 / π ^ 3 := by
  have hrun := prod_Icc_sub_eq_Gamma z hz (1040 * (m + 1) + 1) (560 * (m + 1))
  have hIcc : Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1))
      = Icc (-((1040 * (m + 1) + 1 : ℕ) : ℤ)) ((560 * (m + 1) : ℕ) : ℤ) := by
    congr 1 <;> push_cast <;> ring
  have hq : ((-1 : ℂ) ^ (560 * (m + 1))) = 1 := by
    rw [pow_mul]; norm_num
  rw [hq, one_mul] at hrun
  have hblk : ∀ b ∈ I3.blocks, ∏ k ∈ Icc (3 * b.1 * (m + 1)) (I3.nOf m - 3 * b.1 * (m + 1)),
      (z + (k : ℂ) + 1 / 2) = Complex.Gamma (z + (I3.nOf m - 3 * b.1 * (m + 1) : ℕ) + 3 / 2)
        / Complex.Gamma (z + (3 * b.1 * (m + 1) : ℕ) + 1 / 2) := by
    intro b hb
    have hb1 : b.1 ≤ 46 := (by decide : ∀ b ∈ I3.blocks, b.1 ≤ 46) b hb
    have hb2 : 3 * b.1 * (m + 1) ≤ 138 * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    refine prod_Icc_add_half_eq_Gamma z _ _ (by unfold I3.nOf; omega) (fun k hk => ?_)
    apply hz' (-(k : ℤ) - (3 * b.1 * (m + 1) : ℕ) - 1)
    push_cast at hk ⊢
    linear_combination hk
  unfold RC En
  rw [hIcc, prod_pow, hrun, List.map_congr_left (fun b hb => by rw [hblk b hb])]
  have hinv : (I3.blocks.map (fun b =>
      (Complex.Gamma (z + (I3.nOf m - 3 * b.1 * (m + 1) : ℕ) + 3 / 2)
        / Complex.Gamma (z + (3 * b.1 * (m + 1) : ℕ) + 1 / 2)) ^ b.2)).prod
      = ((I3.blocks.map (fun b =>
      (Complex.Gamma (z + (3 * b.1 * (m + 1) : ℕ) + 1 / 2)
        / Complex.Gamma (z + (I3.nOf m - 3 * b.1 * (m + 1) : ℕ) + 3 / 2)) ^ b.2)).prod)⁻¹ := by
    rw [← list_prod_map_inv]
    exact congrArg List.prod (List.map_congr_left (fun b _ => by rw [← inv_pow, inv_div]))
  rw [hinv, div_inv_eq_mul]
  ring

/-- `P_n(z) = (2z + n + 1) Π_i Γ(s_i z + n u_i + β_i)^{c_i}`. -/
noncomputable def Pfun (m : ℕ) (z : ℂ) : ℂ :=
  (2 * z + (I3.nOf m : ℂ) + 1) *
    ∏ i, Complex.Gamma (sI i * z + (I3.nOf m : ℂ) * uI i + βI i) ^ cI i

lemma En_eq_prod (m : ℕ) (z : ℂ) :
    En m z = ∏ i, Complex.Gamma (sI i * z + (I3.nOf m : ℂ) * uI i + βI i) ^ cI i := by
  simp only [En, I3.blocks, I3.nOf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Fin.prod_univ_succ, Fin.prod_univ_zero, cI, sI, uI, βI]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, zpow_neg, zpow_ofNat, div_pow,
    Fin.succ_zero_eq_one, Matrix.cons_val_one]
  simp (disch := omega) only [Nat.cast_sub]
  push_cast
  ring_nf

/-- **Γ-factorisation in factor-list form.** -/
theorem RC_eq_Pfun (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    RC m z = Pfun m z * Complex.sin (π * z) ^ 3 / π ^ 3 := by
  have h1 : ∀ k : ℤ, z ≠ k := fun k h => hz (by rw [h]; simp)
  have h2 : ∀ k : ℤ, z ≠ k + 1 / 2 := fun k h => hz (by rw [h]; simp)
  rw [RC_eq_En m z h1 h2, En_eq_prod, Pfun]

end BetaIrr.I3.Analytic
