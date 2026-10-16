/-
# Certified bound `max_{x ≥ r} Φ(x) ≤ V_cert = -29.76` (instance I3)

* `Phi_le_V`: `Φ(x) ≤ Vcert = -2976/100` for all `x ≥ 7/6 = r`.
* `Phi_le_tail`: `Φ(x) ≤ Vcert - 4 log(x/3)` for `x ≥ 3`.

Proof: on `(7/6, 4/3]` `Φ'' ≤ 0`, so `Φ` lies below its tangent at `x₀ = 58911/50000`
(`Φ(x₀) ≤ -29.7613`, `-0.002 ≤ Φ'(x₀) ≤ 0`, from `PhiNum`); on `[7/6, x₀]` the tangent is at most
`-29.7613 + 0.002 (x₀ - 7/6) < -29.76`. On `[4/3, ∞)` `Φ' ≤ 0`, and on `[3, ∞)` `Φ' ≤ -4/x`.
(Numerically `max Φ = -29.7613276…` at `x* = 1.1782140…`, PROOF_BETA §9 instance I3.)
Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Size.PhiNum

namespace BetaIrr.I3.Size

open Real Set
open BetaIrr.Size (F continuous_F)

lemma continuous_Phi : Continuous Phi := by
  unfold Phi
  have hF : ∀ c : ℝ, Continuous (fun x : ℝ => F (x + c)) := fun c =>
    continuous_F.comp (continuous_id.add continuous_const)
  refine ((continuous_const.mul (hF _)).sub (continuous_const.mul ?_)).sub ?_
  · simpa [sub_eq_add_neg] using hF (-(7 / 6))
  · have : ∀ l : List (ℕ × ℕ), Continuous (fun x : ℝ =>
        (l.map (fun b => (b.2 : ℝ) * (F (x + 1 - (b.1 : ℝ) / 160) - F (x + (b.1 : ℝ) / 160)))).sum) := by
      intro l
      induction l with
      | nil => simpa using continuous_const
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons]
        refine Continuous.add (continuous_const.mul (Continuous.sub ?_ (hF _))) ih
        simpa [add_sub_assoc] using hF (1 - (a.1 : ℝ) / 160)
    exact this blocks

/-- `Φ'` is antitone on `(7/6, 4/3]`. -/
lemma dPhi_antitoneOn : AntitoneOn dPhi (Ioc (7 / 6) (4 / 3)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := d2Phi) (convex_Ioc _ _)
  · intro x hx
    exact (hasDerivAt_dPhi hx.1).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hasDerivAt_dPhi hx.1).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact d2Phi_nonpos hx.1 hx.2.le

/-- Tangent-line bound on `[7/6, 4/3]` at `x₀ ∈ (7/6, 4/3)`. -/
lemma Phi_le_tangent {x₀ x : ℝ} (h0 : 7 / 6 < x₀) (h0' : x₀ < 4 / 3) (hx : 7 / 6 ≤ x)
    (hx' : x ≤ 4 / 3) : Phi x ≤ Phi x₀ + dPhi x₀ * (x - x₀) := by
  rcases lt_trichotomy x x₀ with h | h | h
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Phi dPhi h continuous_Phi.continuousOn
      (fun y hy => hasDerivAt_Phi (by linarith [hy.1]))
    have hmono : dPhi x₀ ≤ dPhi c :=
      dPhi_antitoneOn ⟨by linarith [hc.1], by linarith [hc.2]⟩ ⟨h0, h0'.le⟩ hc.2.le
    rw [eq_div_iff (by linarith)] at hcd
    nlinarith
  · subst h; simp
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Phi dPhi h continuous_Phi.continuousOn
      (fun y hy => hasDerivAt_Phi (by linarith [hy.1]))
    have hmono : dPhi c ≤ dPhi x₀ :=
      dPhi_antitoneOn ⟨h0, h0'.le⟩ ⟨by linarith [hc.1], by linarith [hc.2]⟩ hc.1.le
    rw [eq_div_iff (by linarith)] at hcd
    nlinarith

lemma Phi_le_V_near {x : ℝ} (hx : 7 / 6 ≤ x) (hx' : x ≤ 4 / 3) : Phi x ≤ (Vcert : ℝ) := by
  have ht := Phi_le_tangent (x₀ := 58911 / 50000) (by norm_num) (by norm_num) hx hx'
  have h1 := Phi_x0_le
  have h2 := dPhi_x0_ge
  have h3 := dPhi_x0_le
  rw [Vcert]; push_cast
  rcases le_total x (58911 / 50000) with h | h
  · nlinarith
  · nlinarith

/-- `Φ` is antitone on `[4/3, ∞)`. -/
lemma Phi_antitoneOn : AntitoneOn Phi (Ici (4 / 3)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := dPhi) (convex_Ici _)
    continuous_Phi.continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    exact (hasDerivAt_Phi (by linarith [mem_Ioi.mp hx])).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx : (4 / 3 : ℝ) < x := hx
    rcases le_total x 3 with h | h
    · exact dPhi_nonpos_of_le hx.le h
    · have := dPhi_le_tail h
      have : -4 / x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
      linarith

/-- **Real-axis bound.** `Φ(x) ≤ V_cert = -29.76` for all `x ≥ r = 7/6`. -/
theorem Phi_le_V {x : ℝ} (hx : 7 / 6 ≤ x) : Phi x ≤ (Vcert : ℝ) := by
  rcases le_total x (4 / 3) with h | h
  · exact Phi_le_V_near hx h
  · have := Phi_antitoneOn Set.self_mem_Ici h h
    have h2 := Phi_le_V_near (x := 4 / 3) (by norm_num) le_rfl
    linarith

/-- **Tail decay.** `Φ(x) ≤ V_cert - 4 log(x/3)` for `x ≥ 3`. -/
theorem Phi_le_tail {x : ℝ} (hx : 3 ≤ x) : Phi x ≤ (Vcert : ℝ) - 4 * Real.log (x / 3) := by
  have hanti : AntitoneOn (fun y => Phi y + 4 * Real.log y) (Ici 3) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun y => dPhi y + 4 * y⁻¹) (convex_Ici _)
    · intro y hy
      have hy : (3 : ℝ) ≤ y := hy
      exact ((hasDerivAt_Phi (by linarith)).continuousAt.add
        ((Real.continuousAt_log (by linarith)).const_mul 4)).continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (3 : ℝ) < y := hy
      exact ((hasDerivAt_Phi (by linarith)).add
        ((Real.hasDerivAt_log (by linarith)).const_mul 4)).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (3 : ℝ) < y := hy
      have := dPhi_le_tail hy.le
      have e : -4 / y = -(4 * y⁻¹) := by ring
      linarith
  have h1 := hanti Set.self_mem_Ici hx hx
  have h2 := Phi_le_V (x := 3) (by norm_num)
  simp only at h1
  rw [Real.log_div (by linarith) (by norm_num)]
  linarith

end BetaIrr.I3.Size
