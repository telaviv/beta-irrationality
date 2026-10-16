/-
# Decay of the concrete I3 integrand (roadmap item A4)

Mirrors `Analytic/ConcreteBound.lean`.

`fC_bound`: for every `c > -1/2` there is `C` with `‖R_n''(z)‖ ≤ C (1 + ‖z‖²)⁻¹` on `Re z ≥ c`.

Route:
* `norm_RC_le`: `‖RC m w‖ ≤ C₁ / ‖w‖³` for `‖w‖ ≥ R₁ = 2(1040(m+1) + 2)`, by comparing every
  linear factor with `‖w‖` (numerator degree `1 + 3·#Zset = 4800(m+1) + 7`, denominator degree
  `Σ B_k = 13392(m+1) + 35`);
* Cauchy's estimate (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) twice, on circles of
  radius `1/2`;
* compactness on `{Re z ≥ c, ‖z‖ ≤ R₁ + 2}`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.Integrand
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Finset Filter Topology Metric
open BetaIrr.Analytic BetaIrr.Fam.Analytic


/-- The radius beyond which the crude factor comparison applies. -/
def R₁ (m : ℕ) : ℝ := 2 * (1040 * ((m : ℝ) + 1) + 2)

lemma one_le_R₁ (m : ℕ) : 1 ≤ R₁ m := by
  unfold R₁; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith

lemma norm_NC_le (m : ℕ) {w : ℂ} (hw : R₁ m ≤ ‖w‖) :
    ‖NC m w‖ ≤ 3 * ‖w‖ * (2 * ‖w‖) ^ (3 * (Zset m).card) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold NC
  rw [norm_mul, norm_prod]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · calc ‖2 * w + (I3.nOf m : ℂ) + 1‖ ≤ ‖2 * w‖ + ‖(I3.nOf m : ℂ)‖ + ‖(1 : ℂ)‖ :=
          norm_add₃_le
      _ = 2 * ‖w‖ + I3.nOf m + 1 := by
          rw [norm_mul, Complex.norm_natCast, norm_one]; norm_num
      _ ≤ 3 * ‖w‖ := by
          have : (I3.nOf m : ℝ) = 480 * ((m : ℝ) + 1) := by unfold I3.nOf; push_cast; ring
          rw [this]; unfold R₁ at hw; linarith
  · rw [pow_mul, ← prod_const]
    refine prod_le_prod₀ (fun _ _ => by positivity) (fun l hl => ?_)
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 3
    have hl' : |(l : ℝ)| ≤ 1040 * ((m : ℝ) + 1) + 1 := by
      unfold Zset at hl
      rw [mem_Icc] at hl
      rw [abs_le]
      constructor
      · have : (-(1040 * ((m : ℤ) + 1)) - 1 : ℤ) ≤ l := hl.1
        have : ((-(1040 * ((m : ℤ) + 1)) - 1 : ℤ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
      · have : l ≤ 560 * ((m : ℤ) + 1) := hl.2
        have : (l : ℝ) ≤ ((560 * ((m : ℤ) + 1) : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
    calc ‖w - (l : ℂ)‖ ≤ ‖w‖ + ‖(l : ℂ)‖ := norm_sub_le _ _
      _ = ‖w‖ + |(l : ℝ)| := by rw [Complex.norm_intCast]
      _ ≤ 2 * ‖w‖ := by unfold R₁ at hw; linarith

lemma norm_DC_ge (m : ℕ) {w : ℂ} (hw : R₁ m ≤ ‖w‖) :
    (‖w‖ / 2) ^ (∑ k ∈ range (I3.nOf m + 1), Bk m k) ≤ ‖DC m w‖ := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold DC
  rw [norm_prod, ← prod_pow_eq_pow_sum]
  refine prod_le_prod₀ (fun _ _ => by positivity) (fun k hk => ?_)
  rw [norm_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have hk' : (k : ℝ) ≤ 480 * ((m : ℝ) + 1) := by
    have := Nat.lt_succ_iff.1 (mem_range.1 hk)
    have : (k : ℝ) ≤ (I3.nOf m : ℝ) := by exact_mod_cast this
    unfold I3.nOf at this; push_cast at this; linarith
  have h1 : ‖w‖ - ((k : ℝ) + 1 / 2) ≤ ‖w + (k : ℂ) + 1 / 2‖ := by
    have := norm_sub_norm_le w (-((k : ℂ) + 1 / 2))
    have e : ‖-((k : ℂ) + 1 / 2)‖ = (k : ℝ) + 1 / 2 := by
      rw [norm_neg, show ((k : ℂ) + 1 / 2) = (((k : ℝ) + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [e, sub_neg_eq_add, ← add_assoc] at this
    exact this
  unfold R₁ at hw
  linarith

/-- `‖RC m w‖ ≤ C₁ / ‖w‖³` for `‖w‖ ≥ R₁`. -/
lemma norm_RC_le (m : ℕ) {w : ℂ} (hw : R₁ m ≤ ‖w‖) :
    ‖RC m w‖ ≤ 3 * 2 ^ (3 * (Zset m).card) * 2 ^ (∑ k ∈ range (I3.nOf m + 1), Bk m k)
      / ‖w‖ ^ 3 := by
  have hw1 : 1 ≤ ‖w‖ := (one_le_R₁ m).trans hw
  have hw0 : 0 < ‖w‖ := by linarith
  set A := 3 * (Zset m).card with hA
  set S := ∑ k ∈ range (I3.nOf m + 1), Bk m k with hS
  have hAS : A + 4 ≤ S := by
    rw [hA, hS, card_Zset, sum_Bk]; omega
  have hD := norm_DC_ge m hw
  have hDpos : 0 < (‖w‖ / 2) ^ S := by positivity
  rw [RC_eq, norm_div]
  rw [div_le_div_iff₀ (hDpos.trans_le hD) (by positivity)]
  calc ‖NC m w‖ * ‖w‖ ^ 3 ≤ 3 * ‖w‖ * (2 * ‖w‖) ^ A * ‖w‖ ^ 3 :=
        mul_le_mul_of_nonneg_right (norm_NC_le m hw) (by positivity)
    _ = 3 * 2 ^ A * 2 ^ S * (‖w‖ / 2) ^ S * ‖w‖ ^ (A + 4) / ‖w‖ ^ S := by
        rw [div_pow]
        field_simp
        ring
    _ ≤ 3 * 2 ^ A * 2 ^ S * (‖w‖ / 2) ^ S := by
        rw [div_le_iff₀ (by positivity)]
        have : ‖w‖ ^ (A + 4) ≤ ‖w‖ ^ S := pow_le_pow_right₀ hw1 hAS
        have hc : 0 ≤ 3 * 2 ^ A * 2 ^ S * (‖w‖ / 2) ^ S := by positivity
        exact mul_le_mul_of_nonneg_left this hc
    _ ≤ 3 * 2 ^ A * 2 ^ S * ‖DC m w‖ := by gcongr

lemma not_mem_poles_of_norm (m : ℕ) {u : ℂ} (hu : R₁ m ≤ ‖u‖) : u ∉ poles m := by
  rintro ⟨k, hk, rfl⟩
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have : ‖-(k : ℂ) - 1 / 2‖ = (k : ℝ) + 1 / 2 := by
    rw [show -(k : ℂ) - 1 / 2 = ((-((k : ℝ) + 1 / 2) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  rw [this] at hu
  have : (k : ℝ) ≤ 480 * ((m : ℝ) + 1) := by
    have : (k : ℝ) ≤ (I3.nOf m : ℝ) := by exact_mod_cast hk
    unfold I3.nOf at this; push_cast at this; linarith
  unfold R₁ at hu
  linarith

/-- Second derivative bound for `‖z‖ ≥ R₁ + 1`: `‖R_n''(z)‖ ≤ 4 C₁ / (‖z‖ - 1)³`. -/
lemma norm_fC_le_far (m : ℕ) {z : ℂ} (hz : R₁ m + 1 ≤ ‖z‖) :
    ‖fC m z‖ ≤ 4 * (3 * 2 ^ (3 * (Zset m).card) *
      2 ^ (∑ k ∈ range (I3.nOf m + 1), Bk m k)) / (‖z‖ - 1) ^ 3 := by
  set C₁ : ℝ := 3 * 2 ^ (3 * (Zset m).card) * 2 ^ (∑ k ∈ range (I3.nOf m + 1), Bk m k)
    with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  have hR := one_le_R₁ m
  have hz1 : 0 < ‖z‖ - 1 := by linarith
  -- points within distance 1 of `z` are far out
  have hfar : ∀ u : ℂ, ‖u - z‖ ≤ 1 → ‖z‖ - 1 ≤ ‖u‖ := by
    intro u hu
    have := norm_sub_norm_le z u
    rw [norm_sub_rev] at hu
    linarith
  have hU := isOpen_compl_poles m
  -- first derivative bound on the circle of radius 1/2 around `z`
  have hd1 : ∀ w ∈ sphere z (1 / 2), ‖deriv (RC m) w‖ ≤ (C₁ / (‖z‖ - 1) ^ 3) / (1 / 2) := by
    intro w hw
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) ?_ ?_
    · refine (RC_differentiableOn m).diffContOnCl_ball (fun u hu => ?_)
      apply not_mem_poles_of_norm
      rw [mem_closedBall, dist_eq_norm] at hu
      rw [mem_sphere, dist_eq_norm] at hw
      have : ‖u - z‖ ≤ 1 := by
        calc ‖u - z‖ = ‖(u - w) + (w - z)‖ := by ring_nf
          _ ≤ ‖u - w‖ + ‖w - z‖ := norm_add_le _ _
          _ ≤ 1 := by linarith
      linarith [hfar u this]
    · intro u hu
      rw [mem_sphere, dist_eq_norm] at hu hw
      have hu' : ‖u - z‖ ≤ 1 := by
        calc ‖u - z‖ = ‖(u - w) + (w - z)‖ := by ring_nf
          _ ≤ ‖u - w‖ + ‖w - z‖ := norm_add_le _ _
          _ ≤ 1 := by linarith
      have h1 := hfar u hu'
      have h2 : R₁ m ≤ ‖u‖ := by linarith
      refine (norm_RC_le m h2).trans ?_
      exact div_le_div_of_nonneg_left hC₁ (by positivity) (pow_le_pow_left₀ hz1.le h1 3)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := deriv (RC m)) (c := z)
    (R := 1 / 2) (by norm_num) ((deriv_RC_differentiableOn m).diffContOnCl_ball (fun u hu => by
      apply not_mem_poles_of_norm
      rw [mem_closedBall, dist_eq_norm] at hu
      have := hfar u (by linarith)
      linarith)) hd1
  unfold fC
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- **A4.** For every `c > -1/2` there is `C` with `‖R_n''(z)‖ ≤ C (1 + ‖z‖²)⁻¹` on `Re z ≥ c`. -/
theorem fC_bound (m : ℕ) {c : ℝ} (hc : -1 / 2 < c) :
    ∃ C : ℝ, ∀ z : ℂ, c ≤ z.re → ‖fC m z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹ := by
  set C₁ : ℝ := 3 * 2 ^ (3 * (Zset m).card) * 2 ^ (∑ k ∈ range (I3.nOf m + 1), Bk m k)
    with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  set R := R₁ m + 2 with hRdef
  have hR1 := one_le_R₁ m
  -- compact part
  have hK : IsCompact ({z : ℂ | c ≤ z.re} ∩ closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const Complex.continuous_re)
  have hcont : ContinuousOn (fC m) ({z : ℂ | c ≤ z.re} ∩ closedBall 0 R) := by
    intro z hz
    refine (fC_differentiableAt m (fun hp => ?_)).continuousAt.continuousWithinAt
    have := re_le_of_mem_poles hp
    have := hz.1
    simp only [Set.mem_ofPred_eq] at this
    linarith
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max M 0 * (1 + R ^ 2) + 64 * C₁, fun z hzre => ?_⟩
  have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hinv0 : 0 ≤ (1 + ‖z‖ ^ 2)⁻¹ := inv_nonneg.2 hpos.le
  by_cases hz : ‖z‖ ≤ R
  · have h1 : ‖fC m z‖ ≤ M := hM z ⟨hzre, by rw [mem_closedBall, dist_zero_right]; exact hz⟩
    have h2 : 1 ≤ (1 + R ^ 2) * (1 + ‖z‖ ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
      have : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      linarith
    calc ‖fC m z‖ ≤ max M 0 := h1.trans (le_max_left _ _)
      _ ≤ max M 0 * ((1 + R ^ 2) * (1 + ‖z‖ ^ 2)⁻¹) :=
          le_mul_of_one_le_right (le_max_right _ _) h2
      _ ≤ max M 0 * (1 + R ^ 2) * (1 + ‖z‖ ^ 2)⁻¹ + 64 * C₁ * (1 + ‖z‖ ^ 2)⁻¹ := by
          have : 0 ≤ 64 * C₁ * (1 + ‖z‖ ^ 2)⁻¹ := by positivity
          linarith [mul_assoc (max M 0) (1 + R ^ 2) (1 + ‖z‖ ^ 2)⁻¹]
      _ = _ := by ring
  · push Not at hz
    have hz2 : R₁ m + 1 ≤ ‖z‖ := by rw [hRdef] at hz; linarith
    have hzge : 2 ≤ ‖z‖ := by rw [hRdef] at hz; linarith
    have hfar := norm_fC_le_far m hz2
    have hhalf : ‖z‖ / 2 ≤ ‖z‖ - 1 := by linarith
    have hcube : (‖z‖ / 2) ^ 3 ≤ (‖z‖ - 1) ^ 3 := pow_le_pow_left₀ (by positivity) hhalf 3
    have hstep : 4 * C₁ / (‖z‖ - 1) ^ 3 ≤ 64 * C₁ * (1 + ‖z‖ ^ 2)⁻¹ := by
      rw [div_le_iff₀ (pow_pos (by linarith) 3)]
      have hz3 : 1 + ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by nlinarith
      have : 4 * C₁ * (1 + ‖z‖ ^ 2) ≤ 64 * C₁ * (‖z‖ / 2) ^ 3 := by
        have : (‖z‖ / 2) ^ 3 = ‖z‖ ^ 3 / 8 := by ring
        rw [this]; nlinarith
      calc 4 * C₁ = 4 * C₁ * (1 + ‖z‖ ^ 2) * (1 + ‖z‖ ^ 2)⁻¹ := by field_simp
        _ ≤ 64 * C₁ * (‖z‖ / 2) ^ 3 * (1 + ‖z‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right this hinv0
        _ ≤ 64 * C₁ * (‖z‖ - 1) ^ 3 * (1 + ‖z‖ ^ 2)⁻¹ := by gcongr
        _ = 64 * C₁ * (1 + ‖z‖ ^ 2)⁻¹ * (‖z‖ - 1) ^ 3 := by ring
    calc ‖fC m z‖ ≤ 4 * C₁ / (‖z‖ - 1) ^ 3 := hfar
      _ ≤ 64 * C₁ * (1 + ‖z‖ ^ 2)⁻¹ := hstep
      _ ≤ (max M 0 * (1 + R ^ 2) + 64 * C₁) * (1 + ‖z‖ ^ 2)⁻¹ := by
          have : 0 ≤ max M 0 * (1 + R ^ 2) := by positivity
          nlinarith

end BetaIrr.I3.Analytic
