/-
# Certified contour data (S1′)–(S5) for instance I3 (PROOF_BETA §6.3)

The contour `Γ_+` (from the real point `x_c` to `+i∞`) consists of
* the lower polyline `dnPts` reversed: `x_c → … → dnStart`, then the connector `[dnStart, eMinus]`;
* the Taylor segment `x₀ + s·dir`, `|s| ≤ ρ = 1/250` (`DirectionI3.lean`), from `eMinus` to `ePlus`;
* the connector `[ePlus, upStart]` and the upper polyline `upStart → … → xtop`;
* the vertical ray `xtop + i y`, `y ≥ 0` (`RayI3.lean`).

This file assembles the kernel checks of `UpChunk1..5.lean`, `DnChunk.lean`, `ConnI3.lean`,
`RayI3.lean` (all `decide +kernel`) into statements about every point of the contour
(`f z = Ψ z - 2πi z`, `h = Re f`, `T0 = -29.78 = -29.7790173 - ηfar`, `ηfar = 9.827·10⁻⁴`,
so `h ≤ T0` gives `h ≤ Re Ω - ηfar` by `I3_ReOmega_ge`):
* **(S2)** `S2_up`, `S2_dn`, `S2_conn_up`, `S2_conn_dn`, `S2_ray`: `h ≤ T0` off the Taylor
  segment; `S2_le_ReOmega` converts to `h ≤ Re Ω - ηfar`.
* **(S4)** `S4_up`, `S4_dn`, `S4_disc`, `S4_conn_up`, `S4_conn_dn` (and `S4_ray`): `|α_i| ≥ 1/1000`
  and `|arg α_i| ≤ 2.76` (`π - 2.76 > 0.38`) for every factor; `Re(2z+1) > 0` (e-factor).
* **(S1′)** `S1'_up`, `S1'_dn`, `xtop_im`: the polylines lie in `Im z > 0` except at `x_c`;
  `xc_mem`: `0 < x_c < 7/6`.
* **(S5)** `S5`: `h(x_c) = Re Ψ(x_c) ≤ T0 < Re Ω`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Interval.DirectionI3
import BetaIrrational.I3.Interval.OmegaI3
import BetaIrrational.I3.Interval.UpChunk1
import BetaIrrational.I3.Interval.UpChunk2
import BetaIrrational.I3.Interval.UpChunk3
import BetaIrrational.I3.Interval.UpChunk4
import BetaIrrational.I3.Interval.UpChunk5
import BetaIrrational.I3.Interval.DnChunk
import BetaIrrational.I3.Interval.RayI3
import BetaIrrational.I3.Interval.ConnI3

namespace BetaIrr.I3.Interval

open Complex Metric BetaIrr.Interval BetaIrr.Interval.IV BetaIrr.Fam.Interval Real

/-- The far margin: `T0 = -29.7790173 - ηfar`. -/
def ηfar : ℚ := 9827 / 10 ^ 7

lemma onPoly_last (a : ℚ × ℚ) (pts : List (ℚ × ℚ)) (h : pts ≠ []) :
    onPoly a pts (toC (pts.getLast h)) := by
  induction pts generalizing a with
  | nil => exact absurd rfl h
  | cons b rest ih =>
    cases rest with
    | nil => left; simpa using right_mem_segment ℝ (toC a) (toC b)
    | cons c rest' => right; simpa using ih b (by simp)

/-! ## Assembling the chunks -/

lemma chk_up : polyChk 40 16 facI3 T0 upStart upPts = true := by
  have e : polyChk 40 16 facI3 T0 upStart upPts =
      (polyChk 40 16 facI3 T0 upStart upC1 && (polyChk 40 16 facI3 T0 upA2 upC2 &&
        (polyChk 40 16 facI3 T0 upA3 upC3 && (polyChk 40 16 facI3 T0 upA4 upC4 &&
          polyChk 40 16 facI3 T0 upA5 upC5)))) := by
    simp only [upPts, polyChk_append]; rfl
  rw [e, chk_up1, chk_up2, chk_up3, chk_up4, chk_up5]; rfl

lemma chk_sec_up : polySectorQ 40 16 amin Amax facI3 upStart upPts = true := by
  have e : polySectorQ 40 16 amin Amax facI3 upStart upPts =
      (polySectorQ 40 16 amin Amax facI3 upStart upC1 &&
        (polySectorQ 40 16 amin Amax facI3 upA2 upC2 &&
        (polySectorQ 40 16 amin Amax facI3 upA3 upC3 &&
        (polySectorQ 40 16 amin Amax facI3 upA4 upC4 &&
          polySectorQ 40 16 amin Amax facI3 upA5 upC5)))) := by
    simp only [upPts, polySectorQ_append]; rfl
  rw [e, chk_sec_up1, chk_sec_up2, chk_sec_up3, chk_sec_up4, chk_sec_up5]; rfl

/-! ## (S2) far part -/

theorem S2_up : ∀ z, onPoly upStart upPts z → (f z).re ≤ T0 :=
  poly_bound 40 16 facI3 T0 upStart upPts chk_up

theorem S2_dn : ∀ z, onPoly dnStart dnPts z → (f z).re ≤ T0 :=
  poly_bound 40 16 facI3 T0 dnStart dnPts chk_dn

lemma Dc_nonneg : (0 : ℝ) ≤ (Dc : ℝ) := by norm_num [Dc]

theorem S2_conn_up : ∀ z ∈ segment ℝ ePlus (toC upStart), (f z).re ≤ T0 := by
  intro z hz
  have hsub := (convex_closedBall (toC upStart) (Dc : ℝ)).segment_subset ePlus_near
    (mem_closedBall_self Dc_nonneg)
  exact ball_bound 40 16 facI3 T0 upStart Dc chk_cup z (hsub hz)

theorem S2_conn_dn : ∀ z ∈ segment ℝ eMinus (toC dnStart), (f z).re ≤ T0 := by
  intro z hz
  have hsub := (convex_closedBall (toC dnStart) (Dc : ℝ)).segment_subset eMinus_near
    (mem_closedBall_self Dc_nonneg)
  exact ball_bound 40 16 facI3 T0 dnStart Dc chk_cdn z (hsub hz)

/-- `T0 = -29.7790173 - ηfar ≤ Re Ω - ηfar`. -/
theorem T0_le_ReOmega : (T0 : ℝ) ≤ Ω.re - ηfar := by
  have := I3_ReOmega_ge
  have e : (T0 : ℝ) = -297790173 / 10 ^ 7 - ηfar := by norm_num [T0, ηfar]
  rw [e]; linarith

theorem S2_le_ReOmega {z : ℂ} (h : (f z).re ≤ T0) : (f z).re ≤ Ω.re - ηfar :=
  h.trans T0_le_ReOmega

/-! ## (S1′) upper half plane, `x_c` -/

lemma chk_im_up : polyImPos upStart upPts = true := by decide +kernel
lemma chk_im_dn : polyImPos dnStart dnPts = true := by decide +kernel

theorem xtop_im : (0 : ℝ) < (toC xtop).im := by simp [toC, xtop]

lemma upPts_last : upPts.getLast (by simp [upPts, upC5]) = xtop := by decide +kernel

theorem xtop_on_up : onPoly upStart upPts (toC xtop) := by
  have := onPoly_last upStart upPts (by simp [upPts, upC5])
  rwa [upPts_last] at this

theorem S1'_up : ∀ z, onPoly upStart upPts z → z ≠ toC xtop → 0 < z.im := by
  intro z hz hne
  refine poly_im_pos upStart upPts chk_im_up (by decide +kernel) z hz ?_
  intro h; apply hne; rw [h]
  have e : (upStart :: upPts).getLast (by simp) = xtop := by decide +kernel
  rw [e]

lemma dnPts_last : dnPts.getLast (by simp [dnPts]) = (xc, 0) := by decide +kernel

theorem S1'_dn : ∀ z, onPoly dnStart dnPts z → z ≠ toC (xc, 0) → 0 < z.im := by
  intro z hz hne
  refine poly_im_pos dnStart dnPts chk_im_dn (by decide +kernel) z hz ?_
  intro h; apply hne; rw [h]
  have e : (dnStart :: dnPts).getLast (by simp) = (xc, 0) := by decide +kernel
  rw [e]

theorem xc_mem : 0 < xc ∧ xc < 7 / 6 := by norm_num [xc]

theorem xc_on_dn : onPoly dnStart dnPts (toC (xc, 0)) := by
  have := onPoly_last dnStart dnPts (by simp [dnPts])
  rwa [dnPts_last] at this

/-- **(S5)** `h(x_c) ≤ T0 < Re Ω`. -/
theorem S5 : (f (toC (xc, 0))).re ≤ T0 ∧ (T0 : ℝ) < Ω.re := by
  refine ⟨S2_dn _ xc_on_dn, ?_⟩
  have := T0_le_ReOmega
  have : (0 : ℝ) < ηfar := by norm_num [ηfar]
  linarith

/-! ## (S4) sector bounds -/

lemma chk_sec_disc : sectorQ 40 16 amin Amax facI3 (CB.ofQRad cRe cIm (ρ + R0)) = true :=
  chk_sec_disc_lit

lemma chk_sec_cup' : sectorQ 40 16 amin Amax facI3 (CB.ofQRad upStart.1 upStart.2 Dc) = true :=
  chk_sec_cup

lemma chk_sec_cdn' : sectorQ 40 16 amin Amax facI3 (CB.ofQRad dnStart.1 dnStart.2 Dc) = true :=
  chk_sec_cdn

theorem S4_up : ∀ z, onPoly upStart upPts z →
    (∀ a ∈ facI3, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax) ∧ -1 / 2 < z.re :=
  poly_sectorQ 40 16 amin Amax facI3 upStart upPts chk_sec_up

theorem S4_dn : ∀ z, onPoly dnStart dnPts z →
    (∀ a ∈ facI3, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax) ∧ -1 / 2 < z.re :=
  poly_sectorQ 40 16 amin Amax facI3 dnStart dnPts chk_sec_dn

/-- On the Taylor disc `closedBall x₀ ρ` (which contains the Taylor segment). -/
theorem S4_disc : ∀ z ∈ closedBall x₀ (ρ : ℝ),
    ∀ a ∈ facI3, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax := by
  intro z hz
  have h := norm_sub_c0_le hz
  have hm : (CB.ofQRad cRe cIm (ρ + R0)).mem z := CB.mem_ofQRad (by simpa [c0] using h)
  exact sector_of_sectorQ 40 16 amin Amax hm chk_sec_disc

theorem S4_conn_up : ∀ z ∈ segment ℝ ePlus (toC upStart),
    ∀ a ∈ facI3, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax := by
  intro z hz
  have hsub := (convex_closedBall (toC upStart) (Dc : ℝ)).segment_subset ePlus_near
    (mem_closedBall_self Dc_nonneg)
  have h := hsub hz
  rw [mem_closedBall, dist_eq_norm] at h
  exact sector_of_sectorQ 40 16 amin Amax (CB.mem_ofQRad (by simpa [toC] using h)) chk_sec_cup'

theorem S4_conn_dn : ∀ z ∈ segment ℝ eMinus (toC dnStart),
    ∀ a ∈ facI3, (amin : ℝ) ≤ ‖a.α z‖ ∧ |arg (a.α z)| ≤ Amax := by
  intro z hz
  have hsub := (convex_closedBall (toC dnStart) (Dc : ℝ)).segment_subset eMinus_near
    (mem_closedBall_self Dc_nonneg)
  have h := hsub hz
  rw [mem_closedBall, dist_eq_norm] at h
  exact sector_of_sectorQ 40 16 amin Amax (CB.mem_ofQRad (by simpa [toC] using h)) chk_sec_cdn'

/-! ## (S2) on the top ray -/

/-- **(S2) on the ray.** -/
theorem S2_ray (y : ℝ) (hy : (xtop.2 : ℝ) ≤ y) : (f ⟨X0, y⟩).re ≤ T0 := by
  have h0 := S2_up _ xtop_on_up
  have e : toC xtop = ⟨X0, xtop.2⟩ := rfl
  rw [e] at h0
  have := S3_h_decreasing le_rfl hy
  have hq := q0_sub_two_pi
  have : 0 ≤ (q0 - 2 * π) * (y - xtop.2) := mul_nonneg (by linarith) (by linarith)
  linarith

end BetaIrr.I3.Interval
