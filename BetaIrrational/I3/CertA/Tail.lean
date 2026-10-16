/-
# The uniform tail bound for `e*` (PROOF_BETA §5.2) for instance I3

For `x ≥ 1` and every `y`:
`f(x, y) ≤ S + 2 + μ_in + G{x} = 40 + G{x}`, hence `e*(x) ≤ 40 + G{x}` (`eStar_le_tail`), and in
particular `e*(x) ≤ E_tail + G{x}` with `E_tail = S + 9 = 44` (the constant used in `CertA.tail`).

Proof (PROOF_BETA §5.2): per block `j`, `[in block] + P_j ≤ 1 + (1 - 2δ_j) x` (in block:
`⌊y-δx⌋ + ⌊(1-δ)x-y⌋ ≤ (1-2δ)x`; out of block: `⌊a⌋ - ⌊b⌋ + [b ∈ ℤ] ≤ a - b + 1`); the run of
odd integers has `c ≥ 3((1+2r)x - 1) = 10x - 3`; and `Σ_j m_j (1 - 2δ_j) = G + 6r + μ_in = G + 10`,
`Σ_j m_j = 35`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.CertA.Attain

namespace BetaIrr.I3.CertA

/-- `⌊a⌋ - ⌊b⌋ + [b ∈ ℤ] ≤ a - b + 1`. -/
lemma floor_sub_floor_ind_le (a b : ℚ) :
    ((⌊a⌋ - ⌊b⌋ + (if Int.fract b = 0 then 1 else 0) : ℤ) : ℚ) ≤ a - b + 1 := by
  have ha := Int.floor_le a
  have hb := Int.sub_one_lt_floor b
  split_ifs with h
  · have hb' : (⌊b⌋ : ℚ) = b := by
      have := Int.self_sub_floor b
      rw [Int.fract] at h
      linarith
    push_cast; linarith
  · push_cast; linarith

/-- One block: `[in block] + P_j ≤ 1 + (1 - 2δ_j) x`. -/
lemma ind_add_Pfun_le (d : ℕ) (x y : ℚ) :
    (((if dlt d * x ≤ y ∧ y ≤ (1 - dlt d) * x then 1 else 0 : ℤ) + Pfun d x y : ℤ) : ℚ)
      ≤ 1 + (1 - 2 * dlt d) * x := by
  unfold Pfun
  by_cases hin : dlt d * x ≤ y ∧ y ≤ (1 - dlt d) * x
  · rw [if_pos hin, if_pos hin]
    have h1 := Int.floor_le (y - dlt d * x)
    have h2 := Int.floor_le ((1 - dlt d) * x - y)
    push_cast; linarith
  · rw [if_neg hin, if_neg hin, zero_add]
    by_cases hlt : y < dlt d * x
    · rw [if_pos hlt]
      have := floor_sub_floor_ind_le ((1 - dlt d) * x - y) (dlt d * x - y)
      have e : (1 - dlt d) * x - y - (dlt d * x - y) + 1 = 1 + (1 - 2 * dlt d) * x := by ring
      rwa [e] at this
    · rw [if_neg hlt]
      have := floor_sub_floor_ind_le (y - dlt d * x) (y - (1 - dlt d) * x)
      have e : y - dlt d * x - (y - (1 - dlt d) * x) + 1 = 1 + (1 - 2 * dlt d) * x := by ring
      rwa [e] at this

/-- The zero run: `c(y) ≥ 10x - 3` for `x ≥ 0`. -/
lemma cfun_ge (x y : ℚ) (hx : 0 ≤ x) : 10 * x - 3 ≤ (cfun x y : ℚ) := by
  unfold cfun
  have hle : 2 * y + 2 * (-(1 + rr)) * x ≤ 2 * y + 2 * rr * x := by unfold rr; nlinarith
  have h := oddCount_eq _ _ hle
  have h1 := Int.sub_one_lt_floor ((2 * y + 2 * rr * x + 1) / 2)
  have h2 := Int.floor_le ((2 * y + 2 * (-(1 + rr)) * x + 1) / 2)
  have h' : ((oddCount (2 * y + 2 * (-(1 + rr)) * x) (2 * y + 2 * rr * x) : ℤ) : ℚ) =
      (⌊(2 * y + 2 * rr * x + 1) / 2⌋ : ℚ) - ⌊(2 * y + 2 * (-(1 + rr)) * x + 1) / 2⌋ := by
    rw [h]; push_cast; ring
  push_cast at h' ⊢
  rw [h']
  unfold rr at h1 h2 ⊢
  linarith

/-- The per-block bounds, summed over any list of blocks. -/
lemma blocks_sum_le (x y : ℚ) (l : List (ℕ × ℕ)) :
    ((((l.map fun b =>
        ((if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then b.2 else 0 : ℕ) : ℤ)).sum : ℤ) : ℚ)
      + (((l.map fun b => (b.2 : ℤ) * Pfun b.1 x y).sum : ℤ) : ℚ))
      ≤ (l.map fun b => (b.2 : ℚ) * (1 + (1 - 2 * dlt b.1) * x)).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hb := ind_add_Pfun_le b.1 x y
    have hmm : (0 : ℚ) ≤ b.2 := by positivity
    have e : ((((if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then b.2 else 0 : ℕ) : ℤ)
        + (b.2 : ℤ) * Pfun b.1 x y : ℤ) : ℚ) =
        (b.2 : ℚ) * (((if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then 1 else 0 : ℤ)
          + Pfun b.1 x y : ℤ) : ℚ) := by
      split_ifs <;> push_cast <;> ring
    have h1 := mul_le_mul_of_nonneg_left hb hmm
    rw [← e] at h1
    push_cast at h1 ih ⊢
    linarith

/-- `Σ_j m_j (1 + (1 - 2δ_j) x) = 35 + (G + 10) x` for the I3 blocks. -/
lemma blocks_weight (x : ℚ) :
    (blocks.map fun b => (b.2 : ℚ) * (1 + (1 - 2 * dlt b.1) * x)).sum = 35 + (G + 10) * x := by
  simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dlt, G]
  push_cast
  ring

/-- **PROOF_BETA §5.2 for I3.** `f(x, y) ≤ 40 + G{x}` for `x ≥ 1`. -/
theorem f_le_tail (x y : ℚ) (hx : 1 ≤ x) : f x y ≤ 40 + G * Int.fract x := by
  unfold f
  rw [if_pos hx]
  have hc := cfun_ge x y (by linarith)
  have hS : ((Sfun x y : ℕ) : ℚ) =
      ((blocks.map fun b =>
        ((if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then b.2 else 0 : ℕ) : ℤ)).sum : ℤ) := by
    rw [← Sfun_cast]; push_cast; rfl
  rw [hS]
  have hsum := blocks_sum_le x y blocks
  rw [blocks_weight] at hsum
  have hfr : (⌊x⌋ : ℚ) = x - Int.fract x := by rw [Int.fract]; ring
  rw [hfr]
  have hG : G = 179 / 10 := rfl
  rw [hG] at hsum ⊢
  nlinarith

/-- **Tail bound for `e*`.** For `x ≥ 1`: `e*(x) ≤ 40 + G{x}`. -/
theorem eStar_le_tail (x : ℚ) (hx : 1 ≤ x) : eStar x ≤ 40 + G * Int.fract x := by
  obtain ⟨⟨y, -, -, hy⟩, -⟩ := eStar_isGreatest x hx
  rw [← hy]
  exact f_le_tail x y hx

end BetaIrr.I3.CertA
