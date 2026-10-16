/-
# Certified saddle data (S0), (S1), (S1′) for instance I3 (PROOF_BETA §6.3)

Instance I3 (`μ_in = 3`, `r = 7/6`, `q = 480`), factor list `facI3` (`FacI3.lean`).

* `c0` = a rational point (25 digits) near the Newton root from the seed `1.1718 + 0.00986 i`
  (the independent Python saddle certificate `d33_saddle_cert.py`, `D33_X0`), `R0 = 10⁻¹²`, `B0 = closedBall c0 R0`;
* `x₀` = **the unique zero of `g = Ψ' - 2πi` in `B0`** (existence and uniqueness:
  `exists_unique_zero_g`, by the contraction `z ↦ z - Y g(z)` of `Interval/Newton.lean`);
  `deriv Ψ x₀ = 2πi`.

Main results:
* `saddle_mem`, `deriv_Ψ_saddle`, `saddle_unique` — (S0);
* `I3_K_ge : 260 ≤ ‖Ψ''(x₀)‖`, `I3_d2_mem` (box for `Ψ''(x₀)`);
* `I3_M_bound : ∀ z ∈ closedBall x₀ ρ, ‖Ψ'''(z)‖ ≤ Mcert` with `ρ = 1/250`, `Mcert ≈ 56745`;
* `I3_rho_M : Mcert * ρ ≤ 3 |Ψ''(x₀)| / 2` — (S1) (`Mcert ρ ≈ 227 ≤ 390`);
* `I3_disc_upper`, `I3_S1'` — (S1′): the Taylor disc lies in `Im z > 0` (`Im x₀ ≈ 0.00997`).

The value `Ω = f(x₀)` and (H4) are in `OmegaI3.lean`. All numerical checks are `decide +kernel`
(no `native_decide`).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Interval.FacI3
import BetaIrrational.Interval.Newton

namespace BetaIrr.I3.Interval

open Complex Metric BetaIrr.Interval BetaIrr.Interval.IV Real

/-! ## Certificate data -/

def cRe : ℚ := 11719231074608510827430178 / 10 ^ 25
def cIm : ℚ := 99732253713548444658806 / 10 ^ 25
/-- The rational centre `c0 ≈ 1.1719231075 + 0.0099732254 i`. -/
noncomputable def c0 : ℂ := ⟨(cRe : ℝ), (cIm : ℝ)⟩
def R0 : ℚ := 1 / 10 ^ 12
/-- `Y ≈ 1 / Ψ''(c0)`. -/
def Yre : ℚ := -1654025977788032 / 10 ^ 18
def Yim : ℚ := -3459625483811011 / 10 ^ 18
noncomputable def Y : ℂ := ⟨(Yre : ℝ), (Yim : ℝ)⟩

/-- Precision parameters: rounding `2^{-80}`, 40 series terms. -/
abbrev pp : ℕ := 80
abbrev nn : ℕ := 40

def P0 : CB := CB.ofQ cRe cIm
def B0box : CB := CB.ofQRad cRe cIm R0
def twoPiI : CB := ⟨ofRat 0, piI.smul 2⟩
def YB : CB := CB.ofQ Yre Yim
def gP : CB := (dpsiB pp nn facI3 P0).sub twoPiI
def d2B : CB := d2psiB facI3 B0box
def KB : CB := (CB.ofQ 1 0).sub (YB.mul d2B)

lemma mem_P0 : P0.mem c0 := CB.mem_ofQ cRe cIm

lemma mem_twoPiI : twoPiI.mem (2 * π * I) := by
  refine ⟨?_, ?_⟩
  · have h : (2 * (π : ℂ) * I).re = ((0 : ℚ) : ℝ) := by simp
    rw [h]; exact mem_ofRat 0
  · have h : (2 * (π : ℂ) * I).im = ((2 : ℚ) : ℝ) * π := by simp
    rw [h]; exact mem_smul 2 mem_piI

lemma mem_YB : YB.mem Y := CB.mem_ofQ Yre Yim

lemma mem_B0box {z : ℂ} (hz : z ∈ closedBall c0 R0) : B0box.mem z := by
  apply CB.mem_ofQRad
  rw [mem_closedBall, dist_eq_norm] at hz
  exact hz

lemma mem_gP : gP.mem (g c0) := CB.mem_sub (mem_dpsiB pp nn facI3 mem_P0) mem_twoPiI

lemma mem_d2B {z : ℂ} (hz : z ∈ closedBall c0 R0) : d2B.mem (d2psiL facI3 z) :=
  mem_d2psiB facI3 (mem_B0box hz)

lemma mem_KB {z : ℂ} (hz : z ∈ closedBall c0 R0) : KB.mem (1 - Y * d2psiL facI3 z) :=
  CB.mem_sub mem_one (CB.mem_mul mem_YB (mem_d2B hz))

/-! ## Kernel-checked numerical facts -/

lemma chk_K : KB.normLe (1 / 10 ^ 6) = true := by decide +kernel
lemma chk_d2 : d2B.normLe 300 = true := by decide +kernel
lemma chk_K_lo : d2B.normGe 260 = true := by decide +kernel
lemma chk_g : gP.normLe (1 / 10 ^ 16) = true := by decide +kernel
lemma chk_Y : YB.normLe 1 = true := by decide +kernel

lemma im_pos_of_mem_ball {z : ℂ} {r : ℝ} (hz : z ∈ closedBall c0 r) (hr : r < cIm) :
    0 < z.im := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h := Complex.abs_im_le_norm (z - c0)
  rw [sub_im] at h
  have : c0.im = cIm := rfl
  rw [this] at h
  have := abs_le.1 (h.trans hz)
  linarith [this.1]

lemma R0_nonneg : (0 : ℝ) ≤ (R0 : ℝ) := by norm_num [R0]

lemma c0_mem : c0 ∈ closedBall c0 (R0 : ℝ) := mem_closedBall_self R0_nonneg

lemma R0_lt : (R0 : ℝ) < cIm := by
  have : R0 < cIm := by norm_num [R0, cIm]
  exact_mod_cast this

lemma im_ne_of_ball {z : ℂ} (hz : z ∈ closedBall c0 R0) : z.im ≠ 0 :=
  (im_pos_of_mem_ball hz R0_lt).ne'

/-! ## (S0): existence and uniqueness of the saddle -/

lemma Y_ne : Y ≠ 0 := by
  intro h
  have : Y.re = 0 := by rw [h]; rfl
  simp [Y, Yre] at this

lemma norm_g_c0 : ‖g c0‖ ≤ ((1 / 10 ^ 16 : ℚ) : ℝ) := CB.norm_le_of_normLe mem_gP chk_g

lemma norm_Yg : ‖Y * g c0‖ ≤ ((1 / 10 ^ 16 : ℚ) : ℝ) := by
  have hY : ‖Y‖ ≤ ((1 : ℚ) : ℝ) := CB.norm_le_of_normLe mem_YB chk_Y
  rw [norm_mul]
  have h0 : (0 : ℝ) ≤ ‖g c0‖ := norm_nonneg _
  push_cast at hY
  calc ‖Y‖ * ‖g c0‖ ≤ 1 * ‖g c0‖ := mul_le_mul_of_nonneg_right hY h0
    _ ≤ _ := by rw [one_mul]; exact norm_g_c0

theorem exists_unique_zero_g : ∃! z, z ∈ closedBall c0 R0 ∧ g z = 0 := by
  have hR : (0 : ℝ) ≤ R0 := by norm_num [R0]
  refine exists_unique_zero_of_contraction (g' := d2psiL facI3) (κ := ((1 / 10 ^ 6 : ℚ) : ℝ))
    (ε := ((1 / 10 ^ 16 : ℚ) : ℝ)) Y_ne hR (fun z hz => I3_hasDerivAt_g (im_ne_of_ball hz))
    (fun z hz => CB.norm_le_of_normLe (mem_KB hz) chk_K) (by norm_num) norm_Yg ?_
  norm_num [R0]

/-- **The saddle point** `x₀`: the unique zero of `Ψ' - 2πi` in `closedBall c0 R0`. -/
noncomputable def x₀ : ℂ := Classical.choose exists_unique_zero_g

lemma x₀_spec : x₀ ∈ closedBall c0 R0 ∧ g x₀ = 0 := (Classical.choose_spec exists_unique_zero_g).1

theorem saddle_mem : x₀ ∈ closedBall c0 R0 := x₀_spec.1

lemma x₀_im_pos : 0 < x₀.im := im_pos_of_mem_ball saddle_mem R0_lt

theorem deriv_Ψ_saddle : deriv Ψ x₀ = 2 * π * I := by
  rw [deriv_Ψ x₀_im_pos.ne']
  have := x₀_spec.2
  simp only [g] at this
  exact sub_eq_zero.1 this

theorem saddle_unique {z : ℂ} (hz : z ∈ closedBall c0 R0) (hd : deriv Ψ z = 2 * π * I) :
    z = x₀ := by
  have hg : g z = 0 := by
    simp only [g]; rw [← deriv_Ψ (im_ne_of_ball hz), hd, sub_self]
  exact (exists_unique_zero_g.unique ⟨hz, hg⟩ x₀_spec)

/-- `‖g‖ ≤ 1/10^16 + 300 R0` on the ball. -/
lemma norm_g_le {z : ℂ} (hz : z ∈ closedBall c0 R0) :
    ‖g z‖ ≤ ((1 / 10 ^ 16 + 300 * R0 : ℚ) : ℝ) := by
  have hmv := (convex_closedBall c0 (R0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := d2psiL facI3) (C := 300)
    (fun w hw => (I3_hasDerivAt_g (im_ne_of_ball hw)).hasDerivWithinAt)
    (fun w hw => by exact_mod_cast CB.norm_le_of_normLe (mem_d2B hw) chk_d2)
    c0_mem hz
  have h0 := norm_g_c0
  have hzc : ‖z - c0‖ ≤ R0 := by rw [← dist_eq_norm]; exact hz
  calc ‖g z‖ = ‖g c0 + (g z - g c0)‖ := by ring_nf
    _ ≤ ‖g c0‖ + ‖g z - g c0‖ := norm_add_le _ _
    _ ≤ ((1 / 10 ^ 16 : ℚ) : ℝ) + 300 * R0 := by nlinarith
    _ = ((1 / 10 ^ 16 + 300 * R0 : ℚ) : ℝ) := by push_cast; ring

/-! ## (S1), (S1′): Taylor disc data -/

/-- Box enclosure of `Ψ''(x₀)`. -/
lemma I3_d2_mem : d2B.mem (d2psiL facI3 x₀) := mem_d2B saddle_mem

/-- **(S1)** `K = |Ψ''(x₀)| ≥ 260`. -/
theorem I3_K_ge : (260 : ℝ) ≤ ‖d2psiL facI3 x₀‖ := by
  have := CB.le_norm_of_normGe I3_d2_mem chk_K_lo
  push_cast at this; exact this

/-- Taylor-disc radius `ρ = 1/250`. -/
def ρ : ℚ := 1 / 250

/-- Lower bounds `m_i` for `|α_i|` on `closedBall x₀ ρ`. -/
def facM : List (Fac × ℚ) :=
  List.zip facI3
    ([3334601, 7273, 1167964, 2167943, 1174214, 2161693, 1180463, 2155443, 1186713, 2149194,
      1192963, 2142944, 1199213, 2136694, 1205463, 2130444, 1211712, 2124194, 1217962, 2117944,
      1230462, 2105444, 1242961, 2092944, 1255461, 2080444, 1267960, 2067945, 1280460, 2055445,
      1292960, 2042945, 1305459, 2030445, 1317959, 2017945, 1330459, 2005445, 1342958, 1992946,
      1355458, 1980446, 1367957, 1967946, 1380457, 1955446, 1392957, 1942946, 1405456, 1930446,
      1417956, 1917947, 1430456, 1905447, 1442956, 1892947, 1455455, 1880447].map
      fun k : ℕ => (k : ℚ) / 10 ^ 6)

lemma facM_fst : facM.map Prod.fst = facI3 := by decide +kernel

/-- The certified bound for `sup |Ψ'''|` on the Taylor disc. -/
def Mcert : ℚ := d3bnd facM

lemma chk_M : d3chk P0 (ρ + R0) facM = true := by decide +kernel

lemma chk_Mρ : Mcert * ρ ≤ 3 * 260 / 2 := by decide +kernel

lemma chk_Mval : Mcert ≤ 56746 := by decide +kernel

lemma norm_sub_c0_le {z : ℂ} (hz : z ∈ closedBall x₀ (ρ : ℝ)) :
    ‖z - c0‖ ≤ ((ρ + R0 : ℚ) : ℝ) := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h0 : ‖x₀ - c0‖ ≤ R0 := by rw [← dist_eq_norm]; exact saddle_mem
  calc ‖z - c0‖ = ‖(z - x₀) + (x₀ - c0)‖ := by ring_nf
    _ ≤ ‖z - x₀‖ + ‖x₀ - c0‖ := norm_add_le _ _
    _ ≤ ρ + R0 := add_le_add hz h0
    _ = ((ρ + R0 : ℚ) : ℝ) := by push_cast; ring

/-- **(S1)** `|Ψ'''| ≤ Mcert` on `closedBall x₀ ρ`. -/
theorem I3_M_bound {z : ℂ} (hz : z ∈ closedBall x₀ (ρ : ℝ)) :
    ‖d3psiL facI3 z‖ ≤ (Mcert : ℝ) := by
  have := norm_d3psiL_le facM mem_P0 (norm_sub_c0_le hz) chk_M
  rw [facM_fst] at this; exact this

/-- **(S1)** `M ρ ≤ 3K/2` with `K ≥ 260`. -/
theorem I3_rho_M : (Mcert : ℝ) * ρ ≤ 3 * ‖d2psiL facI3 x₀‖ / 2 := by
  have h : ((Mcert * ρ : ℚ) : ℝ) ≤ ((3 * 260 / 2 : ℚ) : ℝ) := by exact_mod_cast chk_Mρ
  push_cast at h
  linarith [I3_K_ge]

/-- **(S1′)** the Taylor disc lies in the upper half plane. -/
theorem I3_disc_upper {z : ℂ} (hz : z ∈ closedBall x₀ (ρ : ℝ)) : 0 < z.im := by
  have h := norm_sub_c0_le hz
  have hz' : z ∈ closedBall c0 ((ρ + R0 : ℚ) : ℝ) := by
    rw [mem_closedBall, dist_eq_norm]; exact h
  refine im_pos_of_mem_ball hz' ?_
  have : (ρ + R0 : ℚ) < cIm := by norm_num [ρ, R0, cIm]
  exact_mod_cast this

theorem I3_S1' : 0 < x₀.im - ρ := by
  have h := I3_disc_upper (z := x₀ - (ρ : ℂ) * I) (by
    rw [mem_closedBall, dist_eq_norm]
    have : x₀ - (ρ : ℂ) * I - x₀ = -((ρ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num [ρ])])
  simpa using h

end BetaIrr.I3.Interval
