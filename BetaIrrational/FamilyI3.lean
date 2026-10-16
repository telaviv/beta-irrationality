/-
# The concrete family: parameters, `R_n`, `L_n`, and the assembly from the four inputs

PROOF_BETA §1 and §9 (parameter set "I3"):
* `μ_in = 3`, `r = 7/6`, `q = 480`, `S = 35`, `G = 179/10`, `N = 36`, `e = 1` (S odd);
* pole blocks with offsets `δ = k/160` and multiplicities: `(0, 8)` and `(k, 1)` for
  `k = 1, …, 8` and `k = 10, 12, …, 46`.

With `n = 480(m+1)`: `rn = 560(m+1)`, `(1+r)n = 1040(m+1)`, `δ n = 3k(m+1)`.

Contents:
* the concrete `R_n` and `L_n = Σ_{t ≥ 0} (-1)^t R_n''(t)`;
* the parameter facts `S = 35`, `G` from the blocks, (H1) `G > 0`, (H6) `q(G+1)` even;
* `H5_I3`: `V + A + 20 log 2 < 0` for `V ≤ -29.76` and `A ≤ Acert` (margin ≈ 0.0714);
* `Hyp`, collecting the conclusions of PROOF_BETA Lemmas 3–6 for these `R_n`, `L_n`, and
  `oneOfBeta4To36_of_hyp : Hyp → OneOfBeta4To36`. `Hyp` is built in `I3/Glue/Main.lean`.

Lemma 6(i) uses the real-axis bound `V_cert = -29.76`. The real-axis maximum is
`max_{x ≥ r} Φ = -29.7613276…` at `x* ≈ 1.17821`, certified in `I3/Size/PhiBound.lean`.
Status: complete (no `sorry`).
-/
import BetaIrrational.Defs
import BetaIrrational.Statement
import BetaIrrational.Assembly

namespace BetaIrr

open Filter Topology

/-- **(H5) for instance I3** (μ_in = 3, r = 7/6, so `2(6r + μ_in) = 20`), with the real-axis
bound `V` in place of `Re Ω`: `V + A + 20 log 2 < 0`, margin about `0.0714`. -/
theorem H5_I3 (V A : ℝ) (hV : V ≤ -2976 / 100)
    (hA : A ≤ 12507029707866288048422972493354331 / 790300921079786767495600904601600) :
    V + A + 20 * Real.log 2 < 0 := by
  have hlog := Real.log_two_lt_d9
  norm_num at hlog hA hV ⊢
  linarith

end BetaIrr

namespace BetaIrr.I3

open Filter Topology Finset
open scoped BigOperators

/-- Pole blocks `(k, m)`: offset `δ = k/160`, multiplicity `m`. -/
def blocks : List (ℕ × ℕ) :=
  [(0, 8), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1),
   (10, 1), (12, 1), (14, 1), (16, 1), (18, 1), (20, 1), (22, 1), (24, 1), (26, 1), (28, 1),
   (30, 1), (32, 1), (34, 1), (36, 1), (38, 1), (40, 1), (42, 1), (44, 1), (46, 1)]

/-- The progression `n = 480 (m+1)` (`q = 480`, avoiding `n = 0`). -/
def nOf (m : ℕ) : ℕ := 480 * (m + 1)

/-- `G = Σ_j m_j (1 - 2δ_j) - 6r - μ_in`. -/
def G : ℚ := 179 / 10

/-- `S = Σ_j m_j = 35`, so `N = S + 1 = 36` (S odd). -/
lemma S_eq : (blocks.map Prod.snd).sum = 35 := by decide

/-- `G` agrees with its definition from the parameters (`r = 7/6`, `μ_in = 3`). -/
lemma G_eq : G = (blocks.map (fun b => (b.2 : ℚ) * (1 - 2 * ((b.1 : ℚ) / 160)))).sum
    - 6 * (7 / 6) - 3 := by
  norm_num [G, blocks]

/-- **(H1)** `G > 0`. -/
lemma H1 : 0 < G := by norm_num [G]

/-- **(H6)** `q (G + 1) = 9072` is even, so the parity factor `e` is the same for all `n ∈ 480ℕ`
(here `e = 1`, since `S` is odd). -/
lemma H6 : (480 : ℚ) * (G + 1) = 2 * 4536 := by norm_num [G]

/-- Every block offset satisfies `δ < 1/2` (`k < 80`), so each block `[3k(m+1), n - 3k(m+1)]` is
nonempty and contains the centre. -/
lemma blocks_lt : ∀ b ∈ blocks, b.1 < 80 := by decide

/-- The concrete rational function `R_n(t)` of PROOF_BETA §1 for `n = 480 (m+1)`:
`(2t + n + 1) · Π_{l = -(1+r)n-1}^{rn} (t - l)^3 /`
`Π_j Π_{k = δ_j n}^{(1-δ_j) n} (t + k + 1/2)^{m_j}`,
with `(1+r) n = 1040 (m+1)`, `r n = 560 (m+1)`, `δ_j n = 3 k_j (m+1)`. -/
noncomputable def R (m : ℕ) (t : ℝ) : ℝ :=
  (2 * t + (nOf m : ℝ) + 1) *
    (∏ l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)), (t - (l : ℝ)) ^ 3) /
    (blocks.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)),
        (t + (k : ℝ) + 1 / 2)) ^ b.2)).prod

/-- The linear form `L_n = Σ_{t ≥ 0} (-1)^t R_n''(t)`. -/
noncomputable def L (m : ℕ) : ℝ := ∑' t : ℕ, (-1 : ℝ) ^ t * deriv (deriv (R m)) t

/-- The upper bound of the exact A certificate
(PROOF_BETA §9: X = 400; 62,132 event points, 62,131 intervals). -/
def Acert : ℚ := 12507029707866288048422972493354331 / 790300921079786767495600904601600

/-- The real-axis size constant: `max_{x ≥ r} Φ(x) ≤ Vcert`. -/
def Vcert : ℚ := -2976 / 100

/-- The inputs of the assembly (PROOF_BETA Lemmas 3–6), stated for the concrete `R_n`, `L_n` above;
built in `I3/Glue/Main.lean`. -/
structure Hyp where
  /-- Lemma 3: `L_n ∈ ℚ + ℚ β(4) + … + ℚ β(36)`. -/
  ρ : ℕ → ℚ
  τ : ℕ → ℕ → ℚ
  expansion : ∀ m, L m = (ρ m : ℝ) + ∑ j ∈ Icc 2 18, (τ m j : ℝ) * dirichletBeta (2 * j)
  /-- Lemma 4: a common denominator `D_n` (a positive rational). -/
  D : ℕ → ℚ
  D_pos : ∀ m, 0 < D m
  int_ρ : ∀ m, ∃ z : ℤ, (z : ℚ) = D m * ρ m
  int_τ : ∀ m j, ∃ z : ℤ, (z : ℚ) = D m * τ m j
  /-- (H2): the arithmetic integral, with its certified upper bound. -/
  A : ℝ
  hA : A ≤ (Acert : ℝ)
  /-- Lemmas 4–5: `log D_n ≤ G log n! + n (A + 20 log 2) + o(n)`. -/
  εA : ℕ → ℝ
  εA_lim : Tendsto εA atTop (𝓝 0)
  arith : ∀ᶠ m in atTop, Real.log (D m : ℝ)
    ≤ (G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * (A + 20 * Real.log 2 + εA m)
  /-- Lemma 6(i), real-axis version: `log |L_n| ≤ -G log n! + n V_cert + o(n)`. -/
  εL : ℕ → ℝ
  εL_lim : Tendsto εL atTop (𝓝 0)
  size : ∀ᶠ m in atTop, L m ≠ 0 →
    Real.log |L m| ≤ -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * (Vcert + εL m)
  /-- Lemma 6(ii): `L_n ≠ 0` for infinitely many `n` (via (H4), (H6)). -/
  nonvan : ∃ᶠ m in atTop, L m ≠ 0

/-- **Main theorem (conditional).** The inputs `Hyp` imply that one of `β(4), β(6), …, β(36)` is
irrational. -/
theorem oneOfBeta4To36_of_hyp (H : Hyp) : OneOfBeta4To36 := by
  choose a ha using H.int_ρ
  choose c hc using H.int_τ
  have hform : ∀ m, (a m : ℝ) + ∑ j ∈ Icc 2 18, (c m j : ℝ) * dirichletBeta (2 * j)
      = (H.D m : ℝ) * L m := by
    intro m
    rw [H.expansion m, mul_add, Finset.mul_sum]
    have ha' : (a m : ℝ) = (H.D m : ℝ) * (H.ρ m : ℝ) := by exact_mod_cast ha m
    rw [ha']
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hc' : (c m j : ℝ) = (H.D m : ℝ) * (H.τ m j : ℝ) := by exact_mod_cast hc m j
    rw [hc']
    ring
  have hQ : (Vcert : ℝ) + H.A + 20 * Real.log 2 < 0 :=
    H5_I3 _ H.A (by norm_num [Vcert]) (by simpa [Acert] using H.hA)
  apply oneOfBeta4To36_of_forms a c
  · refine Tendsto.congr (fun m => (hform m).symm) ?_
    refine tendsto_mul_zero_of_log_bound (fun m => (H.D m : ℝ)) L nOf
      (fun m => by unfold nOf; omega) (fun m => by exact_mod_cast H.D_pos m)
      ((Vcert : ℝ) + H.A + 20 * Real.log 2) hQ (fun m => H.εA m + H.εL m)
      (by simpa using H.εA_lim.add H.εL_lim) ?_
    filter_upwards [H.arith, H.size] with m h1 h2 hL
    have h2' := h2 hL
    nlinarith [h1, h2']
  · refine H.nonvan.mono (fun m hm => ?_)
    rw [hform]
    exact mul_ne_zero (by exact_mod_cast (H.D_pos m).ne') hm

end BetaIrr.I3
