/-
# The concrete I3 integrand `R_n''` in the complex plane (roadmap items A1–A3, A5)

Mirrors `Analytic/ConcreteIntegrand.lean`. For `RC m` (the complex extension of `I3.R m`,
`Gamma.lean`):
* block bookkeeping: `Zset` (`#Zset = 1600(m+1) + 2`), `Bk`, `prod_blocks`,
  `sum_Bk : Σ_{k ≤ n} B_k = 13392(m+1) + 35`;
* `RC_eq`: `RC m = NC m / DC m` with `NC = (2z+n+1) Π_{l ∈ Zset} (z-l)³`,
  `DC = Π_{k ≤ n} (z + k + 1/2)^{B_k}`;
* A1 `RC_differentiableAt`, `fC_differentiableAt`: holomorphy off the poles `-k - 1/2`;
* A2 `fC_re_eq`: `Re R_n''(t) = (I3.R m)''(t)` for real `t > -1/2`;
* A3 `fC_conj`: `R_n''(z̄) = conj R_n''(z)`;
* A5 `fC_nat_zero`: `R_n''(t) = 0` for integers `0 ≤ t ≤ 560(m+1)` (triple zeros).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Analytic.Gamma
import BetaIrrational.Analytic.Contour
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false

namespace BetaIrr.I3.Analytic

open Complex Finset Filter Topology Metric
open BetaIrr.Analytic BetaIrr.Fam.Analytic

/-! ### Block bookkeeping for I3 -/

/-- The zero run `[-(1+r)n - 1, rn]`, `(1+r)n = 1040(m+1)`, `rn = 560(m+1)`. -/
def Zset (m : ℕ) : Finset ℤ := Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1))

lemma card_Zset (m : ℕ) : (Zset m).card = 1600 * (m + 1) + 2 := by
  rw [Zset, Int.card_Icc]
  omega

/-- The index interval of block `b = (k, m_j)`: `[3k(m+1), n - 3k(m+1)]`. -/
def blk (m : ℕ) (b : ℕ × ℕ) : Finset ℕ := Icc (3 * b.1 * (m + 1)) (I3.nOf m - 3 * b.1 * (m + 1))

/-- The pole multiplicity `B_k` at `-k - 1/2`. -/
def Bk (m k : ℕ) : ℕ := (I3.blocks.map (fun b => if k ∈ blk m b then b.2 else 0)).sum

lemma blk_subset (m : ℕ) : ∀ b ∈ I3.blocks, blk m b ⊆ range (I3.nOf m + 1) := by
  intro b _ k hk
  simp only [blk, Finset.mem_Icc] at hk
  simp only [Finset.mem_range]
  omega

/-- The block product equals `Π_{k ≤ n} x_k^{B_k}`. -/
lemma prod_blocks {M : Type*} [CommMonoid M] (m : ℕ) (x : ℕ → M) :
    (I3.blocks.map (fun b => (∏ k ∈ blk m b, x k) ^ b.2)).prod
      = ∏ k ∈ range (I3.nOf m + 1), x k ^ Bk m k := by
  rw [prod_list_blocks x (blk m) _ I3.blocks (blk_subset m)]
  rfl

/-- `Σ_{k ≤ n} B_k = 13392(m+1) + 35`. -/
lemma sum_Bk (m : ℕ) : ∑ k ∈ range (I3.nOf m + 1), Bk m k = 13392 * (m + 1) + 35 := by
  simp only [Bk]
  rw [sum_list_blocks (blk m) _ I3.blocks (blk_subset m)]
  simp only [I3.blocks, blk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.card_Icc, I3.nOf]
  omega


/-- Numerator of `RC m`. -/
noncomputable def NC (m : ℕ) (z : ℂ) : ℂ :=
  (2 * z + (I3.nOf m : ℂ) + 1) * ∏ l ∈ Zset m, (z - (l : ℂ)) ^ 3

/-- Denominator of `RC m`. -/
noncomputable def DC (m : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ range (I3.nOf m + 1), (z + (k : ℂ) + 1 / 2) ^ Bk m k

lemma RC_eq (m : ℕ) (z : ℂ) : RC m z = NC m z / DC m z := by
  unfold RC NC DC
  rw [← prod_blocks m (fun k => z + (k : ℂ) + 1 / 2)]
  rfl

/-- The poles `-k - 1/2`, `0 ≤ k ≤ n`. -/
def poles (m : ℕ) : Set ℂ := {z | ∃ k : ℕ, k ≤ I3.nOf m ∧ z = -(k : ℂ) - 1 / 2}

lemma re_le_of_mem_poles {m : ℕ} {z : ℂ} (hz : z ∈ poles m) : z.re ≤ -1 / 2 := by
  obtain ⟨k, _, rfl⟩ := hz
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  simp
  linarith

lemma isOpen_compl_poles (m : ℕ) : IsOpen (poles m)ᶜ := by
  have hfin : (poles m).Finite := by
    have : poles m = (fun k : ℕ => -(k : ℂ) - 1 / 2) '' {k | k ≤ I3.nOf m} := by
      ext z; simp only [poles, Set.mem_image]
      constructor
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    rw [this]
    exact (Set.finite_le_nat _).image _
  exact hfin.isClosed.isOpen_compl

lemma DC_ne_zero (m : ℕ) {z : ℂ} (hz : z ∉ poles m) : DC m z ≠ 0 := by
  unfold DC
  rw [prod_ne_zero_iff]
  intro k hk
  refine pow_ne_zero _ (fun h0 => hz ⟨k, Nat.lt_succ_iff.1 (mem_range.1 hk), ?_⟩)
  linear_combination h0

lemma NC_differentiable (m : ℕ) : Differentiable ℂ (NC m) := by
  unfold NC
  fun_prop

lemma DC_differentiable (m : ℕ) : Differentiable ℂ (DC m) := by
  unfold DC
  fun_prop

/-- A1. -/
lemma RC_differentiableOn (m : ℕ) : DifferentiableOn ℂ (RC m) (poles m)ᶜ := by
  intro z hz
  have h : RC m = fun z => NC m z / DC m z := funext (RC_eq m)
  rw [h]
  exact ((NC_differentiable m z).div (DC_differentiable m z)
    (DC_ne_zero m hz)).differentiableWithinAt

lemma RC_differentiableAt (m : ℕ) {z : ℂ} (hz : z ∉ poles m) : DifferentiableAt ℂ (RC m) z :=
  (RC_differentiableOn m).differentiableAt ((isOpen_compl_poles m).mem_nhds hz)

/-- The complex second derivative `R_n''`. -/
noncomputable def fC (m : ℕ) : ℂ → ℂ := deriv (deriv (RC m))

lemma deriv_RC_differentiableOn (m : ℕ) : DifferentiableOn ℂ (deriv (RC m)) (poles m)ᶜ :=
  (RC_differentiableOn m).deriv (isOpen_compl_poles m)

lemma fC_differentiableOn (m : ℕ) : DifferentiableOn ℂ (fC m) (poles m)ᶜ :=
  (deriv_RC_differentiableOn m).deriv (isOpen_compl_poles m)

lemma fC_differentiableAt (m : ℕ) {z : ℂ} (hz : z ∉ poles m) : DifferentiableAt ℂ (fC m) z :=
  (fC_differentiableOn m).differentiableAt ((isOpen_compl_poles m).mem_nhds hz)

lemma ofReal_not_mem_poles (m : ℕ) {t : ℝ} (ht : -1 / 2 < t) : (t : ℂ) ∉ poles m := by
  intro h
  have := re_le_of_mem_poles h
  simp at this
  linarith

/-- A2. `Re R_n''(t) = (I3.R m)''(t)` for real `t > -1/2`. -/
lemma fC_re_eq (m : ℕ) (t : ℝ) (ht : -1 / 2 < t) :
    (fC m t).re = deriv (deriv (I3.R m)) t := by
  -- first derivative, on the open half line
  have h1 : ∀ x : ℝ, -1 / 2 < x → deriv (I3.R m) x = (deriv (RC m) x).re := by
    intro x hx
    have hd := (RC_differentiableAt m (ofReal_not_mem_poles m hx)).hasDerivAt.real_of_complex
    have he : (fun x : ℝ => (RC m x).re) = I3.R m := by
      funext y; rw [RC_ofReal]; simp
    rw [he] at hd
    exact hd.deriv
  have heq : deriv (I3.R m) =ᶠ[𝓝 t] fun x : ℝ => (deriv (RC m) x).re := by
    filter_upwards [lt_mem_nhds ht] with x hx using h1 x hx
  rw [heq.deriv_eq]
  have hd2 := ((deriv_RC_differentiableOn m).differentiableAt
    ((isOpen_compl_poles m).mem_nhds (ofReal_not_mem_poles m ht))).hasDerivAt.real_of_complex
  exact hd2.deriv.symm

/-! ### Conjugation symmetry (A3) -/

lemma conj_mem_compl_poles (m : ℕ) {z : ℂ} (hz : z ∉ poles m) :
    (starRingEnd ℂ) z ∉ poles m := by
  rintro ⟨k, hk, h⟩
  apply hz
  refine ⟨k, hk, ?_⟩
  have := congrArg (starRingEnd ℂ) h
  rw [Complex.conj_conj] at this
  rw [this]
  simp [map_sub, map_neg, map_natCast, map_ofNat]

lemma RC_conj (m : ℕ) (z : ℂ) : RC m ((starRingEnd ℂ) z) = (starRingEnd ℂ) (RC m z) := by
  rw [RC_eq, RC_eq, map_div₀]
  unfold NC DC
  simp [map_prod, map_pow, map_mul, map_add, map_sub, map_natCast, map_intCast, map_ofNat,
    map_inv₀]

/-- A3. -/
lemma fC_conj (m : ℕ) {z : ℂ} (hz : z ∉ poles m) :
    fC m ((starRingEnd ℂ) z) = (starRingEnd ℂ) (fC m z) := by
  have hU := isOpen_compl_poles m
  have hUc : ∀ z ∈ (poles m)ᶜ, (starRingEnd ℂ) z ∈ (poles m)ᶜ := fun z hz =>
    conj_mem_compl_poles m hz
  have h1 := deriv_conj_symm hU hUc (RC_differentiableOn m) (fun z _ => RC_conj m z)
  exact deriv_conj_symm hU hUc (deriv_RC_differentiableOn m) h1 z hz

/-! ### Triple zeros (A5) -/

/-- A5. `R_n''(t) = 0` for integers `0 ≤ t ≤ 560(m+1)`. -/
lemma fC_nat_zero (m t : ℕ) (ht : t ≤ 560 * (m + 1)) : fC m t = 0 := by
  have htZ : (t : ℤ) ∈ Zset m := by
    unfold Zset; rw [mem_Icc]; constructor <;> omega
  set h : ℂ → ℂ := fun z => (2 * z + (I3.nOf m : ℂ) + 1) *
    (∏ l ∈ (Zset m).erase (t : ℤ), (z - (l : ℂ)) ^ 3) / DC m z with hh
  have hball : ∀ z ∈ ball (t : ℂ) (1 / 2), z ∉ poles m := by
    intro z hz hp
    have h1 := re_le_of_mem_poles hp
    rw [mem_ball, dist_eq_norm] at hz
    have h2 := Complex.abs_re_le_norm (z - t)
    have : (z - t).re = z.re - t := by simp
    rw [this] at h2
    have := (abs_lt.1 (h2.trans_lt hz)).1
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith
  unfold fC
  refine deriv_deriv_eq_zero_of_cube (g := RC m) (h := h) (r := 1 / 2) (by norm_num) ?_ ?_
  · intro z hz
    have hne := DC_ne_zero m (hball z hz)
    rw [hh]
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.div ?_ (DC_differentiable m z) hne
    fun_prop
  · intro z _
    rw [RC_eq, hh, NC]
    rw [← mul_prod_erase _ _ htZ]
    push_cast
    ring

end BetaIrr.I3.Analytic
