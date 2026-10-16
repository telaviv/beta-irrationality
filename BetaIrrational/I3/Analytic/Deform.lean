/-
# Deformation of the concrete contour (roadmap item B1)

`contour_eq_polyline_Fn`: let `c > 0` be a non-integer and `w 0 = c, w 1, …, w K` a polyline
whose points other than `w 0` lie in the open upper half plane, with `Re (w K) > 0`. Then

    i ∫_0^∞ F_n(c + iy) dy = Σ_{k<K} ∫_{[w_k, w_{k+1}]} F_n + i ∫_0^∞ F_n(w_K + iy) dy.

Combined with `L_eq_half_line` this expresses `L_n` through the certified path `nΓ_+`
(with `w_k = n v_k` for `k ≥ 1` and `c = ⌊n x_c⌋ + 1/2`).

Mirrors `Analytic/ConcreteDeform.lean` (instance I3).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.ContourI3
import BetaIrrational.Analytic.Deformation

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Real MeasureTheory Set Filter Topology Metric
open BetaIrr.Analytic BetaIrr.Fam.Analytic


/-- `F_n` is holomorphic at every point of the open upper half plane. -/
lemma Fn_differentiableAt_of_im (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (Fn m) z := by
  have hnp : z ∉ poles m := by
    rintro ⟨k, _, rfl⟩; simp at hz
  unfold Fn Fker
  exact (fC_differentiableAt m hnp).mul (differentiableAt_cscPi (sin_pi_ne_zero_of_im hz.ne'))

/-- `‖F_n(z)‖ ≤ C (1 + ‖z‖²)⁻¹ / Im z` in the upper half plane, `Re z ≥ c`. -/
lemma norm_Fn_le_of_im (m : ℕ) {c C : ℝ}
    (hC : ∀ z : ℂ, c ≤ z.re → ‖fC m z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) {z : ℂ} (hzre : c ≤ z.re)
    (hz : 0 < z.im) : ‖Fn m z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹ * (1 / z.im) := by
  unfold Fn Fker
  rw [norm_mul]
  have h1 := hC z hzre
  have h2 := norm_cscPi_le_of_im z.re z.im hz.ne'
  rw [Complex.re_add_im, abs_of_pos hz] at h2
  have hC0 : 0 ≤ C * (1 + ‖z‖ ^ 2)⁻¹ := (norm_nonneg _).trans h1
  exact mul_le_mul h1 h2 (norm_nonneg _) hC0

theorem contour_eq_polyline_Fn (m : ℕ) {c : ℝ} (hc0 : 0 < c) (hcZ : ∀ k : ℤ, c ≠ k)
    (w : ℕ → ℂ) (K : ℕ) (hw0 : w 0 = c)
    (hseg : ∀ k < K, ∀ t ∈ Ioc (0 : ℝ) 1, 0 < (w k + t * (w (k + 1) - w k)).im)
    (hKim : 0 < (w K).im) (hKre : 0 < (w K).re) :
    I * ∫ y in Ioi (0 : ℝ), Fn m (c + y * I)
      = (∑ k ∈ Finset.range K, segInt (Fn m) (w k) (w (k + 1)))
        + I * ∫ y in Ioi (0 : ℝ), Fn m (w K + y * I) := by
  -- the region `U = {Im > 0} ∪ B(c, δ)`
  set δ : ℝ := min (c - ⌊c⌋) (⌈c⌉ - c) / 2 with hδ
  have hfl : (⌊c⌋ : ℝ) < c := lt_of_le_of_ne (Int.floor_le c) (fun h => hcZ _ h.symm)
  have hcl : c < (⌈c⌉ : ℝ) := lt_of_le_of_ne (Int.le_ceil c) (fun h => hcZ _ h)
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min (by linarith) (by linarith))
  have hδ1 : δ ≤ (c - ⌊c⌋) / 2 := by rw [hδ]; gcongr; exact min_le_left _ _
  have hδ2 : δ ≤ (⌈c⌉ - c) / 2 := by rw [hδ]; gcongr; exact min_le_right _ _
  have hceil : (⌈c⌉ : ℝ) ≤ ⌊c⌋ + 1 := by exact_mod_cast Int.ceil_le_floor_add_one c
  set U : Set ℂ := {z : ℂ | 0 < z.im} ∪ ball (c : ℂ) δ with hU
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).union isOpen_ball
  -- points of the ball: real part near `c`
  have hball_re : ∀ z ∈ ball (c : ℂ) δ, c - δ < z.re ∧ z.re < c + δ := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (z - c)
    have : (z - c).re = z.re - c := by simp
    rw [this] at h
    have := abs_lt.1 (h.trans_lt hz)
    constructor <;> linarith [this.1, this.2]
  have hFdiff : DifferentiableOn ℂ (Fn m) U := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases hz with hz | hz
    · exact Fn_differentiableAt_of_im m hz
    · obtain ⟨h1, h2⟩ := hball_re z hz
      have hnp : z ∉ poles m := fun hp => by
        have := re_le_of_mem_poles hp; linarith
      have hsin : Complex.sin (π * z) ≠ 0 := by
        refine sin_pi_ne_zero_of_re (fun k hk => ?_)
        rw [hk] at h1 h2
        have hk1 : (⌊c⌋ : ℝ) < k := by linarith
        have hk2 : (k : ℝ) < ⌈c⌉ := by linarith
        have hk1' : ⌊c⌋ < k := by exact_mod_cast hk1
        have hk2' : k < ⌈c⌉ := by exact_mod_cast hk2
        have : ⌈c⌉ ≤ ⌊c⌋ + 1 := Int.ceil_le_floor_add_one c
        omega
      unfold Fn Fker
      exact (fC_differentiableAt m hnp).mul (differentiableAt_cscPi hsin)
  obtain ⟨P, hP⟩ := exists_prim_upper_union_ball (F := Fn m) c δ hδ0 hFdiff
  -- bounds
  set c' : ℝ := min c (w K).re with hc'
  have hc'0 : 0 < c' := lt_min hc0 hKre
  obtain ⟨C, hC⟩ := fC_bound m (c := c') (by linarith)
  have hC0 : 0 ≤ C := by
    have := hC ((c : ℂ)) (by simp [hc'])
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (by positivity)
  rw [show (c : ℂ) = w 0 from hw0.symm]
  refine ray_eq_polyline_add_ray hUopen hFdiff hP w K ?_ ?_ ?_ ?_ ?_ (fun Y => C / Y)
    (tendsto_const_nhds.div_atTop tendsto_id) ?_
  · -- segments lie in `U`
    intro k hk t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; rw [hw0]; right; exact (mem_ball_self hδ0 : (c : ℂ) ∈ ball (c : ℂ) δ)
      · left
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk0
        have := hseg j (by omega) 1 ⟨one_pos, le_rfl⟩
        simp only [Complex.ofReal_one, one_mul, add_sub_cancel] at this
        simpa using this
    · left; exact hseg k hk t ⟨h0, ht.2⟩
  · -- ray from `c`
    intro y hy
    rcases eq_or_lt_of_le hy with h0 | h0
    · subst h0; rw [hw0]; right; simpa using (mem_ball_self hδ0 : (c : ℂ) ∈ ball (c : ℂ) δ)
    · left; rw [hw0]; simpa using h0
  · -- ray from `w K`
    intro y hy; left; simp; linarith
  · -- integrability on the ray from `c`
    have hsc : Real.sin (π * c) ≠ 0 := by
      intro h0
      rw [Real.sin_eq_zero_iff] at h0
      obtain ⟨k, hk⟩ := h0
      exact hcZ k (mul_right_cancel₀ Real.pi_ne_zero
        (by rw [hk]; ring : (k : ℝ) * π = c * π)).symm
    obtain ⟨C₂, hC₂⟩ := fC_bound m (c := c) (by linarith)
    have hdiff : DifferentiableOn ℂ (fC m) {z : ℂ | -1 / 2 < z.re} := fun z hz =>
      (fC_differentiableAt m (fun hp => by
        have := re_le_of_mem_poles hp
        simp only [Set.mem_ofPred_eq] at hz
        linarith)).differentiableWithinAt
    have := integrable_Fker_line (c₀ := -1 / 2) hdiff hC₂ c le_rfl (by linarith) hsc
    rw [hw0]
    exact this.integrableOn
  · -- integrability on the ray from `w K`
    have hbound : ∀ y ∈ Ioi (0 : ℝ), ‖Fn m (w K + y * I)‖ ≤
        C * (1 / (w K).im) * (1 + y ^ 2)⁻¹ := by
      intro y hy
      have hy0 : 0 < y := hy
      have him : (w K + y * I).im = (w K).im + y := by simp
      have hre : (w K + y * I).re = (w K).re := by simp
      have h := norm_Fn_le_of_im m hC (z := w K + y * I) (by rw [hre]; exact min_le_right _ _)
        (by rw [him]; linarith)
      rw [him] at h
      refine h.trans ?_
      have h1 : (1 + ‖w K + y * I‖ ^ 2)⁻¹ ≤ (1 + y ^ 2)⁻¹ := by
        apply inv_anti₀ (by positivity)
        have := Complex.abs_im_le_norm (w K + y * I)
        rw [him, abs_of_pos (by linarith)] at this
        have : y ^ 2 ≤ ‖w K + y * I‖ ^ 2 := pow_le_pow_left₀ hy0.le (by linarith) 2
        linarith
      have h2 : 1 / ((w K).im + y) ≤ 1 / (w K).im :=
        one_div_le_one_div_of_le hKim (by linarith)
      calc C * (1 + ‖w K + y * I‖ ^ 2)⁻¹ * (1 / ((w K).im + y))
          ≤ C * (1 + y ^ 2)⁻¹ * (1 / (w K).im) := by gcongr
        _ = C * (1 / (w K).im) * (1 + y ^ 2)⁻¹ := by ring
    have hcont : ContinuousOn (fun y : ℝ => Fn m (w K + y * I)) (Ioi 0) := by
      intro y hy
      have hy0 : 0 < y := hy
      have : 0 < (w K + y * I).im := by simp; linarith
      exact (ContinuousAt.comp (g := Fn m) (f := fun y : ℝ => w K + y * I)
        (Fn_differentiableAt_of_im m this).continuousAt (by fun_prop)).continuousWithinAt
    exact (integrable_inv_one_add_sq.const_mul _).integrableOn.mono'
      (hcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  · -- horizontal segments
    filter_upwards [eventually_gt_atTop 0] with Y hY
    intro t ht
    set z := w 0 + Y * I + t * (((w K).re - (w 0).re : ℝ) : ℂ) with hz
    have him : z.im = Y := by rw [hz, hw0]; simp
    have hre : z.re = c + t * ((w K).re - c) := by rw [hz, hw0]; simp
    have hzre : c' ≤ z.re := by
      rw [hre]
      rcases le_total c (w K).re with h | h
      · have : 0 ≤ t * ((w K).re - c) := mul_nonneg ht.1 (by linarith)
        have : c' ≤ c := min_le_left _ _
        linarith
      · have : c' ≤ (w K).re := min_le_right _ _
        have : t * ((w K).re - c) ≥ (w K).re - c := by nlinarith [ht.2]
        linarith
    refine ⟨Or.inl (by rw [Set.mem_ofPred_eq]; rw [him]; exact hY), ?_⟩
    have h := norm_Fn_le_of_im m hC hzre (by rw [him]; exact hY)
    rw [him] at h
    refine h.trans ?_
    have : (1 + ‖z‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖z‖])
    calc C * (1 + ‖z‖ ^ 2)⁻¹ * (1 / Y) ≤ C * 1 * (1 / Y) := by gcongr
      _ = C / Y := by ring

end BetaIrr.I3.Analytic
