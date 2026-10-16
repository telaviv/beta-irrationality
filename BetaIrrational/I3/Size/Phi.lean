/-
# The real-axis exponent `Φ` of instance I3 (PROOF_BETA §8 Lemma 6(i), elementary version)

`Φ(x) = 3[F(x + 13/6) - F(x - 7/6)] - Σ_j m_j [F(x + 1 - δ_j) - F(x + δ_j)]`, `F(y) = y log y`,
with `r = 7/6` and the I3 pole blocks `δ_j = k_j/160`, multiplicities `m_j` (`I3.blocks`).

Here: definitions of `Φ`, `Φ'`, `Φ''`, derivative lemmas, and the qualitative shape:
* `Φ'' ≤ 0` on `(7/6, 4/3]` (`d2Phi_nonpos`, three sub-intervals with monotone bounds);
* `Φ' ≤ 0` on `[4/3, 3]` (`dPhi_nonpos_of_le`) and `Φ'(x) ≤ -4/x` on `[3, ∞)` (`dPhi_le_tail`).
(Numerically `Φ'' ≤ 0` on `(7/6, 1.5566]`, and `x Φ'(x) ∈ [-17.9, -14.7]` on `[3, ∞)`.)

The generic facts about `F` and list sums are in `Size/Common.lean`.
Status: complete (no `sorry`).
-/
import BetaIrrational.FamilyI3
import BetaIrrational.Size.Common

namespace BetaIrr.I3.Size

open Real Set
open BetaIrr.Size (F continuous_F hasDerivAt_F F_tangent hasDerivAt_list_sum list_sum_le log_blk_ge)

/-- The real-axis exponent `Φ`. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  3 * F (x + 13 / 6) - 3 * F (x - 7 / 6) -
    (blocks.map (fun b => (b.2 : ℝ) * (F (x + 1 - (b.1 : ℝ) / 160) - F (x + (b.1 : ℝ) / 160)))).sum

/-- `Φ'`. -/
noncomputable def dPhi (x : ℝ) : ℝ :=
  3 * Real.log (x + 13 / 6) - 3 * Real.log (x - 7 / 6) -
    (blocks.map (fun b => (b.2 : ℝ) *
      (Real.log (x + 1 - (b.1 : ℝ) / 160) - Real.log (x + (b.1 : ℝ) / 160)))).sum

/-- `Φ''`. -/
noncomputable def d2Phi (x : ℝ) : ℝ :=
  3 * (x + 13 / 6)⁻¹ - 3 * (x - 7 / 6)⁻¹ -
    (blocks.map (fun b => (b.2 : ℝ) * ((x + 1 - (b.1 : ℝ) / 160)⁻¹ - (x + (b.1 : ℝ) / 160)⁻¹))).sum

lemma blk_le (b : ℕ × ℕ) (hb : b ∈ blocks) : b.1 ≤ 46 := by
  have h : ∀ b ∈ blocks, b.1 ≤ 46 := by decide
  exact h b hb

lemma blk_d_le (b : ℕ × ℕ) (hb : b ∈ blocks) : (b.1 : ℝ) / 160 ≤ 46 / 160 := by
  have := blk_le b hb
  have : (b.1 : ℝ) ≤ 46 := by exact_mod_cast this
  linarith

lemma blk_pos {x : ℝ} (hx : 0 < x) (b : ℕ × ℕ) (hb : b ∈ blocks) :
    0 < x + 1 - (b.1 : ℝ) / 160 ∧ 0 < x + (b.1 : ℝ) / 160 := by
  have := blk_d_le b hb
  have : (0 : ℝ) ≤ (b.1 : ℝ) / 160 := by positivity
  constructor <;> linarith

lemma hasDerivAt_Phi {x : ℝ} (hx : 7 / 6 < x) : HasDerivAt Phi (dPhi x) x := by
  have hF : ∀ c : ℝ, 0 < x + c → HasDerivAt (fun y => F (y + c)) (Real.log (x + c) + 1) x := by
    intro c hc
    exact (hasDerivAt_F hc.ne').comp_add_const x c
  have h1 := (hF (13 / 6) (by linarith)).const_mul 3
  have h2 := (hF (-(7 / 6)) (by linarith)).const_mul 3
  have h3 := hasDerivAt_list_sum blocks
    (fun b y => (b.2 : ℝ) * (F (y + 1 - (b.1 : ℝ) / 160) - F (y + (b.1 : ℝ) / 160)))
    (fun b y => (b.2 : ℝ) * ((Real.log (y + (1 - (b.1 : ℝ) / 160)) + 1)
      - (Real.log (y + (b.1 : ℝ) / 160) + 1))) x (by
      intro b hb
      obtain ⟨hp1, hp2⟩ := blk_pos (by linarith) b hb
      have e1 := hF (1 - (b.1 : ℝ) / 160) (by linarith)
      have e2 := hF ((b.1 : ℝ) / 160) hp2
      have := (e1.sub e2).const_mul (b.2 : ℝ)
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Pi.sub_apply, add_sub_assoc])
  have := (h1.sub h2).sub h3
  unfold Phi dPhi
  refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))).congr_deriv ?_
  · simp only [Pi.sub_apply, ← sub_eq_add_neg]
  · congr 1
    · simp only [sub_eq_add_neg]; ring
    · congr 1
      apply List.map_congr_left
      intro b _
      simp only [add_sub_assoc]
      ring

lemma hasDerivAt_dPhi {x : ℝ} (hx : 7 / 6 < x) : HasDerivAt dPhi (d2Phi x) x := by
  have hL : ∀ c : ℝ, 0 < x + c → HasDerivAt (fun y => Real.log (y + c)) (x + c)⁻¹ x := by
    intro c hc
    exact (Real.hasDerivAt_log hc.ne').comp_add_const x c
  have h1 := (hL (13 / 6) (by linarith)).const_mul 3
  have h2 := (hL (-(7 / 6)) (by linarith)).const_mul 3
  have h3 := hasDerivAt_list_sum blocks
    (fun b y => (b.2 : ℝ) * (Real.log (y + 1 - (b.1 : ℝ) / 160) - Real.log (y + (b.1 : ℝ) / 160)))
    (fun b y => (b.2 : ℝ) * ((y + (1 - (b.1 : ℝ) / 160))⁻¹ - (y + (b.1 : ℝ) / 160)⁻¹)) x (by
      intro b hb
      obtain ⟨hp1, hp2⟩ := blk_pos (by linarith) b hb
      have e1 := hL (1 - (b.1 : ℝ) / 160) (by linarith)
      have e2 := hL ((b.1 : ℝ) / 160) hp2
      have := (e1.sub e2).const_mul (b.2 : ℝ)
      refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Pi.sub_apply, add_sub_assoc])
  have := (h1.sub h2).sub h3
  unfold dPhi d2Phi
  refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))).congr_deriv ?_
  · simp only [Pi.sub_apply, ← sub_eq_add_neg]
  · simp only [← sub_eq_add_neg, add_sub_assoc]

/-- Monotone bound for `Φ''` on `[a, b]` (`7/6 ≤ a`, `x > 7/6`). -/
lemma d2Phi_le_crude {a b x : ℝ} (ha : 7 / 6 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hx : 7 / 6 < x) :
    d2Phi x ≤ 3 * (a + 13 / 6)⁻¹ - 3 * (b - 7 / 6)⁻¹ -
      (blocks.map (fun b' => (b'.2 : ℝ) *
        ((b + 1 - (b'.1 : ℝ) / 160)⁻¹ - (a + (b'.1 : ℝ) / 160)⁻¹))).sum := by
  unfold d2Phi
  have e1 : 3 * (x + 13 / 6)⁻¹ ≤ 3 * (a + 13 / 6)⁻¹ := by
    have : 0 < a + 13 / 6 := by linarith
    gcongr
  have e2 : 3 * (b - 7 / 6)⁻¹ ≤ 3 * (x - 7 / 6)⁻¹ := by
    have : 0 < x - 7 / 6 := by linarith
    gcongr
  have e3 := list_sum_le blocks
    (fun b' => (b'.2 : ℝ) * ((b + 1 - (b'.1 : ℝ) / 160)⁻¹ - (a + (b'.1 : ℝ) / 160)⁻¹))
    (fun b' => (b'.2 : ℝ) * ((x + 1 - (b'.1 : ℝ) / 160)⁻¹ - (x + (b'.1 : ℝ) / 160)⁻¹)) (by
      intro b' hb
      obtain ⟨hp1, hp2⟩ := blk_pos (x := x) (by linarith) b' hb
      have hd0 : (0 : ℝ) ≤ (b'.1 : ℝ) / 160 := by positivity
      have hm : (0 : ℝ) ≤ (b'.2 : ℝ) := by positivity
      apply mul_le_mul_of_nonneg_left _ hm
      have : (b + 1 - (b'.1 : ℝ) / 160)⁻¹ ≤ (x + 1 - (b'.1 : ℝ) / 160)⁻¹ := by
        apply inv_anti₀ hp1; linarith
      have : (x + (b'.1 : ℝ) / 160)⁻¹ ≤ (a + (b'.1 : ℝ) / 160)⁻¹ := by
        apply inv_anti₀ (by linarith); linarith
      linarith)
  linarith

/-- `Φ'' ≤ 0` on `(7/6, 4/3]`: monotone bounds on `[7/6, 6/5]`, `[6/5, 5/4]`, `[5/4, 4/3]`. -/
lemma d2Phi_nonpos {x : ℝ} (hx : 7 / 6 < x) (hx' : x ≤ 4 / 3) : d2Phi x ≤ 0 := by
  rcases le_total x (6 / 5) with h1 | h1
  · have := d2Phi_le_crude (a := 7 / 6) (b := 6 / 5) le_rfl hx.le h1 hx
    simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    norm_num at this
    linarith
  rcases le_total x (5 / 4) with h2 | h2
  · have := d2Phi_le_crude (a := 6 / 5) (b := 5 / 4) (by norm_num) h1 h2 hx
    simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    norm_num at this
    linarith
  · have := d2Phi_le_crude (a := 5 / 4) (b := 4 / 3) (by norm_num) h2 hx' hx
    simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    norm_num at this
    linarith

/-- `Sb(x) = Σ_j m_j (1 - 2δ_j)/(x + 1 - δ_j) ≤ Σ_j m_j [log(x+1-δ_j) - log(x+δ_j)]`. -/
lemma sumblk_ge {x : ℝ} (hx : 0 < x) :
    (blocks.map (fun b => (b.2 : ℝ) * ((1 - 2 * ((b.1 : ℝ) / 160)) / (x + 1 - (b.1 : ℝ) / 160)))).sum ≤
    (blocks.map (fun b => (b.2 : ℝ) *
      (Real.log (x + 1 - (b.1 : ℝ) / 160) - Real.log (x + (b.1 : ℝ) / 160)))).sum := by
  apply list_sum_le
  intro b hb
  obtain ⟨hp1, hp2⟩ := blk_pos hx b hb
  exact mul_le_mul_of_nonneg_left (log_blk_ge hp1 hp2) (by positivity)

/-- Monotonicity of `Sb`: for `x ≤ c`, `Sb(c) ≤ Sb(x)`. -/
lemma sumblk_anti {x c : ℝ} (hx : 0 < x) (hxc : x ≤ c) :
    (blocks.map (fun b => (b.2 : ℝ) * ((1 - 2 * ((b.1 : ℝ) / 160)) / (c + 1 - (b.1 : ℝ) / 160)))).sum ≤
    (blocks.map (fun b => (b.2 : ℝ) * ((1 - 2 * ((b.1 : ℝ) / 160)) / (x + 1 - (b.1 : ℝ) / 160)))).sum := by
  apply list_sum_le
  intro b hb
  obtain ⟨hp1, _⟩ := blk_pos hx b hb
  have hd := blk_d_le b hb
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_left (by linarith) hp1 (by linarith)

lemma dPhi_eq {x : ℝ} (hx : 7 / 6 < x) : dPhi x = 3 * Real.log ((x + 13 / 6) / (x - 7 / 6)) -
    (blocks.map (fun b => (b.2 : ℝ) *
      (Real.log (x + 1 - (b.1 : ℝ) / 160) - Real.log (x + (b.1 : ℝ) / 160)))).sum := by
  unfold dPhi
  rw [Real.log_div (by linarith) (by linarith)]
  ring

lemma log24_eq : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
  rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  push_cast; ring

lemma log6_eq : Real.log 6 = Real.log 2 + Real.log 3 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

/-- `Φ' ≤ 0` on `[4/3, 3]`. -/
lemma dPhi_nonpos_of_le {x : ℝ} (hx : 4 / 3 ≤ x) (hx2 : x ≤ 3) : dPhi x ≤ 0 := by
  have hx0 : 7 / 6 < x := by linarith
  rw [dPhi_eq hx0]
  have hS := sumblk_ge (x := x) (by linarith)
  have l2 := Real.log_two_lt_d9
  have l3 := Real.log_three_lt_d9
  rcases le_total x 2 with h2 | h2
  · -- `x ∈ [4/3, 2]`: ratio `≤ 21 ≤ 24`
    have hr : (x + 13 / 6) / (x - 7 / 6) ≤ 24 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hlog : Real.log ((x + 13 / 6) / (x - 7 / 6)) ≤ Real.log 24 :=
      Real.log_le_log (div_pos (by linarith) (by linarith)) hr
    have hA := sumblk_anti (x := x) (c := 2) (by linarith) h2
    have hv : (blocks.map (fun b => (b.2 : ℝ) *
        ((1 - 2 * ((b.1 : ℝ) / 160)) / (2 + 1 - (b.1 : ℝ) / 160)))).sum ≥ 955 / 100 := by
      simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      norm_num
    have := log24_eq
    norm_num at l2 l3
    linarith
  · -- `x ∈ [2, 3]`: ratio `≤ 5 ≤ 6`
    have hr : (x + 13 / 6) / (x - 7 / 6) ≤ 6 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hlog : Real.log ((x + 13 / 6) / (x - 7 / 6)) ≤ Real.log 6 :=
      Real.log_le_log (div_pos (by linarith) (by linarith)) hr
    have hA := sumblk_anti (x := x) (c := 3) (by linarith) hx2
    have hv : (blocks.map (fun b => (b.2 : ℝ) *
        ((1 - 2 * ((b.1 : ℝ) / 160)) / (3 + 1 - (b.1 : ℝ) / 160)))).sum ≥ 7 := by
      simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      norm_num
    have := log6_eq
    norm_num at l2 l3
    linarith

/-- Tail: `Φ'(x) ≤ -4/x` for `x ≥ 3`. -/
lemma dPhi_le_tail {x : ℝ} (hx : 3 ≤ x) : dPhi x ≤ -4 / x := by
  have hx0 : 7 / 6 < x := by linarith
  have hxp : 0 < x := by linarith
  rw [dPhi_eq hx0]
  have hS := sumblk_ge (x := x) hxp
  have hr := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < x + 13 / 6)
    (by linarith : 0 < x - 7 / 6))
  have e1 : (x + 13 / 6) / (x - 7 / 6) - 1 = (10 / 3) / (x - 7 / 6) := by
    have : x - 7 / 6 ≠ 0 := by linarith
    rw [div_sub_one this]; ring_nf
  have e2 : (10 / 3) / (x - 7 / 6) ≤ (10 / 3) * (18 / 11) / x := by
    rw [div_le_div_iff₀ (by linarith) hxp]; nlinarith
  have hT : (blocks.map (fun b => (b.2 : ℝ) * (1 - 2 * ((b.1 : ℝ) / 160)) * (3 / (4 * x)))).sum ≤
      (blocks.map (fun b => (b.2 : ℝ) *
        ((1 - 2 * ((b.1 : ℝ) / 160)) / (x + 1 - (b.1 : ℝ) / 160)))).sum := by
    apply list_sum_le
    intro b hb
    obtain ⟨hp1, _⟩ := blk_pos hxp b hb
    have hd := blk_d_le b hb
    have hd0 : (0 : ℝ) ≤ (b.1 : ℝ) / 160 := by positivity
    have h1 : 3 / (4 * x) ≤ 1 / (x + 1 - (b.1 : ℝ) / 160) := by
      rw [div_le_div_iff₀ (by positivity) hp1]; linarith
    have h2 : (0 : ℝ) ≤ 1 - 2 * ((b.1 : ℝ) / 160) := by linarith
    calc (b.2 : ℝ) * (1 - 2 * ((b.1 : ℝ) / 160)) * (3 / (4 * x))
        = (b.2 : ℝ) * ((1 - 2 * ((b.1 : ℝ) / 160)) * (3 / (4 * x))) := by ring
      _ ≤ (b.2 : ℝ) * ((1 - 2 * ((b.1 : ℝ) / 160)) * (1 / (x + 1 - (b.1 : ℝ) / 160))) := by
          gcongr
      _ = (b.2 : ℝ) * ((1 - 2 * ((b.1 : ℝ) / 160)) / (x + 1 - (b.1 : ℝ) / 160)) := by ring
  rw [List.sum_map_mul_right] at hT
  have hv : (blocks.map (fun b => (b.2 : ℝ) * (1 - 2 * ((b.1 : ℝ) / 160)))).sum = 279 / 10 := by
    simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num
  rw [hv] at hT
  have e3 : (279 / 10 : ℝ) * (3 / (4 * x)) = (837 / 40) / x := by
    field_simp; ring
  have e5 : 3 * ((10 / 3) * (18 / 11) / x) - (837 / 40) / x ≤ -4 / x := by
    have : 3 * ((10 / 3) * (18 / 11) / x) - (837 / 40) / x = (-2007 / 440) / x := by ring
    rw [this, div_le_div_iff_of_pos_right hxp]; norm_num
  linarith

end BetaIrr.I3.Size
