/-
# `eStar x` is exactly `sup_{0 ≤ y ≤ x} f(x, y)`, and it is constant on event intervals (I3)


* `eStar_isGreatest`: for `x ≥ 1`, `eStar x` is the greatest element of `{f x y | 0 ≤ y ≤ x}`
  (PROOF_BETA §5.1: `e*(x) := sup_{0≤y≤x} f(x, y)`; the sup is attained).
* `eStar_eq_mid`: for consecutive events `a < b` and `x ∈ (a, b)`, `e*(x) = e*((a+b)/2)`
  (PROOF_BETA §5.3).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.CertA.Step

namespace BetaIrr.I3.CertA

lemma foldl_inv {α : Type*} (step : ℤ → α → ℤ) (P : ℤ → Prop)
    (h : ∀ acc a, P acc → P (step acc a)) :
    ∀ (l : List α) (init : ℤ), P init → P (l.foldl step init)
  | [], _, hi => hi
  | a :: l, init, hi => foldl_inv step P h l _ (h init a hi)

/-- `v` is realised: `v - G⌊x⌋ = f x y` for some `0 ≤ y ≤ x`. -/
def Realized (x : ℚ) (v : ℤ) : Prop := ∃ y, 0 ≤ y ∧ y ≤ x ∧ f x y = (v : ℚ) - G * ⌊x⌋

lemma valid_spec (P Q M k ri : ℤ) (hQ : 0 < Q) (hMdef : M = 960 * Q) (hM : ri < M)
    (right : Bool) (hv : valid (P / Q) (960 * (P % Q)) ri k right = true) :
    0 ≤ k ∧ (if right then k * M + ri < 960 * P else k * M + ri ≤ 960 * P) := by
  have hPQ := Int.emod_add_ediv_mul P Q
  have hr0 : 0 ≤ P % Q := Int.emod_nonneg _ (by omega)
  have hrQ : P % Q < Q := Int.emod_lt_of_pos _ hQ
  have hX : 960 * P = (P / Q) * M + 960 * (P % Q) := by subst hMdef; linarith
  have hMpos : 0 < M := by omega
  unfold valid at hv
  have hk0 : 0 ≤ k := by cases right <;> simp at hv <;> exact hv.1
  refine ⟨hk0, ?_⟩
  rcases lt_or_ge k (P / Q) with hlt | hge
  · have : (k + 1) * M ≤ (P / Q) * M := mul_le_mul_of_nonneg_right (by omega) (by omega)
    cases right <;> simp <;> nlinarith
  · have heq : k = P / Q := by cases right <;> simp at hv <;> omega
    subst heq
    cases right <;> simp at hv ⊢ <;> omega

lemma floor_div_bounds (N M : ℤ) (hM : 0 < M) :
    ⌊(N : ℚ) / M⌋ * M ≤ N ∧ N < (⌊(N : ℚ) / M⌋ + 1) * M := by
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  have h1 := Int.floor_le ((N : ℚ) / M)
  have h2 := Int.lt_floor_add_one ((N : ℚ) / M)
  rw [le_div_iff₀ hM'] at h1
  rw [div_lt_iff₀ hM'] at h2
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

lemma realized_cand (x : ℚ) (hx : 1 ≤ x) (k ri : ℤ) (h0 : 0 ≤ ri) (hM : ri < 960 * x.den)
    (right : Bool) (hv : valid (x.num / x.den) (960 * (x.num % x.den)) ri k right = true) :
    Realized x (phiAt (preOf x.num x.den) (qrOf x.num x.den c1Off) (qrOf x.num x.den c2Off)
      k ri right) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  obtain ⟨hk0, hle⟩ := valid_spec x.num x.den (960 * x.den) k ri hQ rfl hM right hv
  set M : ℤ := 960 * (x.den : ℤ) with hMdef
  have hMpos : 0 < M := by omega
  have hMq : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hMpos
  have hxs : x = ((960 * x.num : ℤ) : ℚ) / (M : ℚ) := x_eq_scaled x
  have hc : candY x k ri = ((k * M + ri : ℤ) : ℚ) / (M : ℚ) := candY_eq x k ri
  have hc0 : 0 ≤ candY x k ri := by
    rw [hc]; apply div_nonneg _ hMq.le
    have : 0 ≤ k * M + ri := by nlinarith
    exact_mod_cast this
  cases right
  · simp only [Bool.false_eq_true, if_false] at hle
    refine ⟨candY x k ri, hc0, ?_, ?_⟩
    · rw [hc]
      conv_rhs => rw [hxs]
      apply div_le_div_of_nonneg_right _ hMq.le
      exact_mod_cast hle
    · rw [f_eq_Phi _ _ hx, phiAt_eq_Phi x k ri h0 hM false]
      simp
  · simp only [if_true] at hle
    set y := candY x k ri + 1 / (2 * (M : ℚ))
    have hsub : ∀ o : ℤ × ℤ, y - offVal x o =
        (((2 * ((k - (qrOf x.num x.den o).1) * M + ri - (qrOf x.num x.den o).2) + 1 : ℤ)) : ℚ)
          / ((2 * M : ℤ) : ℚ) := by
      intro o
      have := candY_sub x k ri o
      rw [← hMdef] at this
      simp only [y]
      rw [show candY x k ri + 1 / (2 * (M : ℚ)) - offVal x o =
        (candY x k ri - offVal x o) + 1 / (2 * (M : ℚ)) by ring, this]
      field_simp
      push_cast
      ring
    have hfl : ∀ o : ℤ × ℤ, ⌊y - offVal x o⌋ = ⌊candY x k ri - offVal x o⌋ := by
      intro o
      rw [hsub, candY_sub]
      set N := (k - (qrOf x.num x.den o).1) * M + ri - (qrOf x.num x.den o).2
      obtain ⟨b1, b2⟩ := floor_div_bounds N M hMpos
      apply floor_div_eq _ _ _ (by omega) <;> nlinarith
    have hcl : ∀ o : ℤ × ℤ, ⌈y - offVal x o⌉ = ⌊candY x k ri - offVal x o⌋ + 1 := by
      intro o
      rw [hsub, candY_sub]
      set N := (k - (qrOf x.num x.den o).1) * M + ri - (qrOf x.num x.den o).2
      obtain ⟨b1, b2⟩ := floor_div_bounds N M hMpos
      apply ceil_div_eq _ _ _ (by omega) <;> nlinarith
    refine ⟨y, ?_, ?_, ?_⟩
    · simp only [y]; positivity
    · have : y = (((2 * (k * M + ri) + 1 : ℤ)) : ℚ) / ((2 * M : ℤ) : ℚ) := by
        simp only [y]; rw [hc]; field_simp; push_cast; ring
      rw [this]
      conv_rhs => rw [hxs, show ((960 * x.num : ℤ) : ℚ) / (M : ℚ) =
        ((1920 * x.num : ℤ) : ℚ) / ((2 * M : ℤ) : ℚ) by push_cast; field_simp; ring]
      apply div_le_div_of_nonneg_right _ (by push_cast; positivity)
      exact_mod_cast (by omega : 2 * (k * M + ri) + 1 ≤ 1920 * x.num)
    · rw [f_eq_Phi _ _ hx, phiAt_eq_Phi x k ri h0 hM true]
      simp only [if_true]
      congr 3
      · funext o; exact hfl o
      · funext o; exact hcl o

/-- The computed integer max is realised by some `y ∈ [0, x]`. -/
lemma eStarInt_realized (x : ℚ) (hx : 1 ≤ x) : Realized x (eStarInt x) := by
  have hQ : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  unfold eStarInt
  dsimp only
  have hstep : ∀ (ri : ℤ), 0 ≤ ri → ri < 960 * x.den → ∀ (right : Bool) (acc k : ℤ),
      Realized x acc → Realized x (candStep (preOf x.num x.den) (qrOf x.num x.den c1Off)
        (qrOf x.num x.den c2Off) (x.num / x.den) (960 * (x.num % x.den)) ri right acc k) := by
    intro ri h0 hM right acc k hacc
    unfold candStep
    split_ifs with hv
    · rcases max_choice acc (phiAt (preOf x.num x.den) (qrOf x.num x.den c1Off)
          (qrOf x.num x.den c2Off) k ri right) with h | h
      · rw [h]; exact hacc
      · rw [h]; exact realized_cand x hx k ri h0 hM right hv
    · exact hacc
  apply foldl_inv _ (Realized x)
  · intro acc o hacc
    obtain ⟨-, hr0, hrM⟩ := qrOf_spec x.num x.den hQ o
    apply foldl_inv _ (Realized x) (fun acc k h => hstep _ hr0 hrM true acc k h)
    apply foldl_inv _ (Realized x) (fun acc k h => hstep _ hr0 hrM false acc k h)
    exact hacc
  · refine ⟨0, le_rfl, by linarith, ?_⟩
    have := phiAt_eq_Phi x 0 0 le_rfl (by omega) false
    have hc : candY x 0 0 = 0 := by simp [candY]
    rw [hc] at this
    rw [f_eq_Phi _ _ hx, this]
    simp

/-- **`e*(x) = max_{0 ≤ y ≤ x} f(x, y)`** (PROOF_BETA §5.1), for `x ≥ 1`. -/
theorem eStar_isGreatest (x : ℚ) (hx : 1 ≤ x) :
    IsGreatest {v | ∃ y, 0 ≤ y ∧ y ≤ x ∧ f x y = v} (eStar x) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy0, hyx, hy⟩ := eStarInt_realized x hx
    exact ⟨y, hy0, hyx, by rw [hy, eStar, if_pos hx]⟩
  · rintro v ⟨y, hy0, hyx, rfl⟩
    exact f_le_eStar x y hx hy0 hyx

/-- **Step function (PROOF_BETA §5.3).** `e*` is constant on each open event interval:
`e*(x) = e*((a+b)/2)` for consecutive events `a < b` and `a < x < b`. -/
theorem eStar_eq_mid (a b : ℚ) (hc : Consec (events 400) a b) (x : ℚ) (hax : a < x)
    (hxb : x < b) : eStar x = eStar ((a + b) / 2) := by
  have ha := (events_bounds a hc.mem_left).1
  have hab := hc.lt (events_pairwise 400)
  have hm : a < (a + b) / 2 ∧ (a + b) / 2 < b := ⟨by linarith, by linarith⟩
  have hx1 : 1 ≤ x := by linarith
  have hm1 : 1 ≤ (a + b) / 2 := by linarith
  apply le_antisymm
  · obtain ⟨⟨y, hy0, hyx, hy⟩, -⟩ := eStar_isGreatest x hx1
    rw [← hy]
    exact f_le_eStar_mid a b hc x hax hxb y hy0 hyx
  · obtain ⟨⟨y, hy0, hyx, hy⟩, -⟩ := eStar_isGreatest _ hm1
    rw [← hy]
    obtain ⟨hst, hfl⟩ := sameType_of_consec a b ((a + b) / 2) x hc hm ⟨hax, hxb⟩
    exact f_le_eStar_of_sameType _ x hm1 hx1 hfl hst y hy0 hyx

end BetaIrr.I3.CertA
