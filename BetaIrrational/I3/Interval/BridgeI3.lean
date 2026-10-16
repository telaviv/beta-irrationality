/-
# Bridge: the I3 interval certificate in the vocabulary of `I3/Analytic/`

`I3/Analytic/Factors.lean` indexes the I3 factor list by `Fin 58` (`cI`, `sI`, `uI`,
`alphaI`) and defines `PsiI`, `Psi1I`, `Psi2I`, `Psi3I`, `phaseI`, `SectorAt`. This file proves that
they agree with the list-based `Ψ`, `dpsiL`, `d2psiL`, `d3psiL`, `f` of the interval certificate
(through the enumeration `facA` of `facI3` and the generic `Fam/Interval/ListSum.lean`), and
restates the certified saddle data (S0)–(S5) in those terms. (PROOF_BETA §6.2–6.3.)

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Interval.ContourI3
import BetaIrrational.I3.Analytic.Factors
import BetaIrrational.Fam.Interval.ListSum

namespace BetaIrr.I3.Interval

open Complex Metric Real BetaIrr.Interval BetaIrr.Fam.Interval
open BetaIrr.I3.Analytic (cI sI uI alphaI PsiI Psi1I Psi2I Psi3I phaseI SectorAt)

/-- The factor list in the `I3/Analytic/` order (the same order as `facI3`). -/
def facA : Fin 58 → Fac :=
  ![⟨3, 1, 13 / 6⟩, ⟨3, -1, 7 / 6⟩, ⟨8, 1, 0⟩, ⟨-8, 1, 1⟩,
    ⟨1, 1, 1 / 160⟩, ⟨-1, 1, 159 / 160⟩, ⟨1, 1, 2 / 160⟩, ⟨-1, 1, 158 / 160⟩,
    ⟨1, 1, 3 / 160⟩, ⟨-1, 1, 157 / 160⟩, ⟨1, 1, 4 / 160⟩, ⟨-1, 1, 156 / 160⟩,
    ⟨1, 1, 5 / 160⟩, ⟨-1, 1, 155 / 160⟩, ⟨1, 1, 6 / 160⟩, ⟨-1, 1, 154 / 160⟩,
    ⟨1, 1, 7 / 160⟩, ⟨-1, 1, 153 / 160⟩, ⟨1, 1, 8 / 160⟩, ⟨-1, 1, 152 / 160⟩,
    ⟨1, 1, 10 / 160⟩, ⟨-1, 1, 150 / 160⟩, ⟨1, 1, 12 / 160⟩, ⟨-1, 1, 148 / 160⟩,
    ⟨1, 1, 14 / 160⟩, ⟨-1, 1, 146 / 160⟩, ⟨1, 1, 16 / 160⟩, ⟨-1, 1, 144 / 160⟩,
    ⟨1, 1, 18 / 160⟩, ⟨-1, 1, 142 / 160⟩, ⟨1, 1, 20 / 160⟩, ⟨-1, 1, 140 / 160⟩,
    ⟨1, 1, 22 / 160⟩, ⟨-1, 1, 138 / 160⟩, ⟨1, 1, 24 / 160⟩, ⟨-1, 1, 136 / 160⟩,
    ⟨1, 1, 26 / 160⟩, ⟨-1, 1, 134 / 160⟩, ⟨1, 1, 28 / 160⟩, ⟨-1, 1, 132 / 160⟩,
    ⟨1, 1, 30 / 160⟩, ⟨-1, 1, 130 / 160⟩, ⟨1, 1, 32 / 160⟩, ⟨-1, 1, 128 / 160⟩,
    ⟨1, 1, 34 / 160⟩, ⟨-1, 1, 126 / 160⟩, ⟨1, 1, 36 / 160⟩, ⟨-1, 1, 124 / 160⟩,
    ⟨1, 1, 38 / 160⟩, ⟨-1, 1, 122 / 160⟩, ⟨1, 1, 40 / 160⟩, ⟨-1, 1, 120 / 160⟩,
    ⟨1, 1, 42 / 160⟩, ⟨-1, 1, 118 / 160⟩, ⟨1, 1, 44 / 160⟩, ⟨-1, 1, 116 / 160⟩,
    ⟨1, 1, 46 / 160⟩, ⟨-1, 1, 114 / 160⟩]

lemma ofFn_facA : List.ofFn facA = facI3 := by decide +kernel

lemma facA_mem (i : Fin 58) : facA i ∈ facI3 := by
  rw [← ofFn_facA]; exact List.mem_ofFn.2 ⟨i, rfl⟩

lemma facA_c : ∀ i, (facA i).c = cI i := by decide +kernel

lemma facA_s (i : Fin 58) : (((facA i).s : ℤ) : ℝ) = sI i := by
  fin_cases i <;> simp [facA, sI]

lemma facA_κ (i : Fin 58) : (((facA i).κ : ℚ) : ℝ) = uI i := by
  fin_cases i <;> simp [facA, uI]

lemma facA_sC (i : Fin 58) : ((facA i).s : ℂ) = ((sI i : ℝ) : ℂ) := by
  rw [← facA_s]; push_cast; rfl

lemma facA_κC (i : Fin 58) : ((facA i).κ : ℂ) = ((uI i : ℝ) : ℂ) := by
  rw [← facA_κ]; push_cast; rfl

lemma facA_cC (i : Fin 58) : ((facA i).c : ℂ) = ((cI i : ℤ) : ℂ) := by rw [facA_c]

lemma alphaI_eq (i : Fin 58) (x : ℂ) : alphaI i x = (facA i).α x := by
  simp only [alphaI, Fac.α, facA_sC, facA_κC]

theorem alphaI_mem (i : Fin 58) (x : ℂ) : ∃ a ∈ facI3, alphaI i x = a.α x :=
  ⟨facA i, facA_mem i, alphaI_eq i x⟩

theorem PsiI_eq (x : ℂ) : PsiI x = Ψ x := by
  have h := sum_fin_eq_list facA (fun a => (a.c : ℂ) * (a.α x * log (a.α x)))
  rw [ofFn_facA, ← psiL_eq_sum] at h
  rw [Ψ, ← h, PsiI]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [alphaI_eq, facA_cC]

theorem Psi1I_eq (x : ℂ) : Psi1I x = dpsiL facI3 x := by
  have hcs : ∑ i, ((cI i : ℂ) * ((sI i : ℝ) : ℂ)) = 0 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) BetaIrr.I3.Analytic.sum_cs
    push_cast at this; exact this
  have h := sum_fin_eq_list facA (fun a => (a.c : ℂ) * ((a.s : ℂ) * (log (a.α x) + 1)))
  rw [ofFn_facA, ← dpsiL_eq_sum] at h
  rw [← h]
  calc Psi1I x = Psi1I x + ∑ i, ((cI i : ℂ) * ((sI i : ℝ) : ℂ)) := by rw [hcs, add_zero]
    _ = ∑ i, ((cI i : ℂ) * ((sI i : ℝ) : ℂ) * log (alphaI i x)
          + (cI i : ℂ) * ((sI i : ℝ) : ℂ)) := by
        rw [Psi1I, ← Finset.sum_add_distrib]
    _ = _ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [alphaI_eq, facA_cC, facA_sC]; ring

theorem Psi2I_eq (x : ℂ) : Psi2I x = d2psiL facI3 x := by
  have h := sum_fin_eq_list facA (fun a => (a.c : ℂ) * ((a.s : ℂ) * (a.s : ℂ) / a.α x))
  rw [ofFn_facA, ← d2psiL_eq_sum] at h
  rw [← h, Psi2I]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [alphaI_eq, facA_cC, facA_sC]; ring

theorem Psi3I_eq (x : ℂ) : Psi3I x = d3psiL facI3 x := by
  have h := sum_fin_eq_list facA
    (fun a => (a.c : ℂ) * (-((a.s : ℂ) * (a.s : ℂ) * (a.s : ℂ)) / a.α x ^ 2))
  rw [ofFn_facA, ← d3psiL_eq_sum] at h
  rw [← h, Psi3I, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [alphaI_eq, facA_cC, facA_sC]; ring

theorem phaseI_eq (x : ℂ) : phaseI x = f x := by
  simp only [phaseI, f, PsiI_eq]

/-- The sector condition of `I3/Analytic/` from the list form, with `a = 1/1000`,
`η = π - 2.76 > 0.38`. -/
theorem sectorAt_of {x : ℂ}
    (h : ∀ a ∈ facI3, ((amin : ℚ) : ℝ) ≤ ‖a.α x‖ ∧ |arg (a.α x)| ≤ ((Amax : ℚ) : ℝ)) :
    SectorAt (1 / 1000) (π - 276 / 100) x := by
  intro i
  obtain ⟨a, ha, e⟩ := alphaI_mem i x
  rw [e]
  have := h a ha
  constructor
  · have h1 := this.1; norm_num [amin] at h1; exact h1
  · have h2 := this.2; norm_num [Amax] at h2; linarith

theorem eta_pos : (38 / 100 : ℝ) < π - 276 / 100 := by
  have := Real.pi_gt_d2; linarith

/-! ## (S0)/(S1) in `I3/Analytic/` notation -/

theorem saddle_Psi1I : Psi1I x₀ = 2 * π * I := by
  rw [Psi1I_eq]; have := x₀_spec.2; simp only [g] at this; exact sub_eq_zero.1 this

theorem saddle_Psi2I_dir : Psi2I x₀ * dir ^ 2 = -(Kx : ℂ) := by
  rw [Psi2I_eq]; exact dir_sq

theorem Kx_eq : Kx = ‖Psi2I x₀‖ := by rw [Psi2I_eq]; rfl

theorem Psi3I_bound {z : ℂ} (hz : z ∈ closedBall x₀ (ρ : ℝ)) : ‖Psi3I z‖ ≤ (Mcert : ℝ) := by
  rw [Psi3I_eq]; exact I3_M_bound hz

theorem rho_M_Kx : (Mcert : ℝ) * ρ ≤ 3 * Kx / 2 := I3_rho_M

theorem phase_saddle : phaseI x₀ = Ω := by rw [phaseI_eq]; rfl

theorem sector_disc {z : ℂ} (hz : z ∈ closedBall x₀ (ρ : ℝ)) :
    SectorAt (1 / 1000) (π - 276 / 100) z :=
  sectorAt_of (S4_disc z hz)

/-! ## (S2), (S4) along the contour in `I3/Analytic/` notation -/

/-- Points of the certified contour other than the Taylor segment. -/
def OnFar (z : ℂ) : Prop :=
  onPoly upStart upPts z ∨ onPoly dnStart dnPts z ∨ z ∈ segment ℝ ePlus (toC upStart) ∨
    z ∈ segment ℝ eMinus (toC dnStart) ∨ ∃ y : ℝ, (xtop.2 : ℝ) ≤ y ∧ z = ⟨X0, y⟩

theorem far_phase {z : ℂ} (hz : OnFar z) : (phaseI z).re ≤ Ω.re - ηfar := by
  rw [phaseI_eq]
  refine S2_le_ReOmega ?_
  rcases hz with h | h | h | h | ⟨y, hy, rfl⟩
  · exact S2_up z h
  · exact S2_dn z h
  · exact S2_conn_up z h
  · exact S2_conn_dn z h
  · exact S2_ray y hy

theorem far_sector {z : ℂ} (hz : OnFar z) : SectorAt (1 / 1000) (π - 276 / 100) z := by
  rcases hz with h | h | h | h | ⟨y, hy, rfl⟩
  · exact sectorAt_of (S4_up z h).1
  · exact sectorAt_of (S4_dn z h).1
  · exact sectorAt_of (S4_conn_up z h)
  · exact sectorAt_of (S4_conn_dn z h)
  · exact sectorAt_of (S4_ray y hy)

/-- (S3) in `I3/Analytic/` notation: `Im Ψ' ≥ q0 = 7 > 2π + 0.71` on the top ray. -/
theorem top_ray_Psi1I (y : ℝ) (hy : (xtop.2 : ℝ) ≤ y) : (q0 : ℝ) ≤ (Psi1I ⟨X0, y⟩).im := by
  rw [Psi1I_eq]; exact S3_ray y hy

end BetaIrr.I3.Interval
