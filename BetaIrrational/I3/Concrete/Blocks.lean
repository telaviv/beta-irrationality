/-
# Instance I3: block bookkeeping

Facts about the block-membership count `I3.Bk` (PROOF_BETA §1):
* `prod_blocks`: `Π_j (Π_{k ∈ block j} x_k)^{m_j} = Π_{k ≤ n} x_k^{B_k}` (any commutative monoid);
* `Bk_le`: `B_k ≤ S = 35`; `Bk_ge`: `B_k ≥ 8` for `k ≤ n`;
* `Bk_mirror`: `B_{n-k} = B_k`;
* `sum_Bk`: `Σ_{k ≤ n} B_k = 13392(m+1) + 35` (odd).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Concrete.Data

namespace BetaIrr.I3

open Finset
open scoped BigOperators

/-- The index interval of block `b = (k, m_j)`: `[3k(m+1), n - 3k(m+1)]`. -/
def blk (m : ℕ) (b : ℕ × ℕ) : Finset ℕ := Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1))

lemma Bk_eq (m k : ℕ) : Bk m k = (blocks.map (fun b => if k ∈ blk m b then b.2 else 0)).sum := by
  simp only [Bk, blk, Finset.mem_Icc]

/-- Reorganising a product of block products (general list version). -/
lemma prod_list_blocks {M : Type*} [CommMonoid M] (x : ℕ → M) (I : ℕ × ℕ → Finset ℕ)
    (U : Finset ℕ) (L : List (ℕ × ℕ)) (hsub : ∀ b ∈ L, I b ⊆ U) :
    (L.map (fun b => (∏ k ∈ I b, x k) ^ b.2)).prod
      = ∏ k ∈ U, x k ^ (L.map (fun b => if k ∈ I b then b.2 else 0)).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, Finset.prod_mul_distrib]
    rw [ih (fun b' hb' => hsub b' (List.mem_cons_of_mem _ hb'))]
    congr 1
    simp only [pow_ite, pow_zero]
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr (hsub b (List.mem_cons_self ..)),
      Finset.prod_pow]

/-- Additive version: counting with multiplicity. -/
lemma sum_list_blocks (I : ℕ × ℕ → Finset ℕ) (U : Finset ℕ) (L : List (ℕ × ℕ))
    (hsub : ∀ b ∈ L, I b ⊆ U) :
    ∑ k ∈ U, (L.map (fun b => if k ∈ I b then b.2 else 0)).sum
      = (L.map (fun b => b.2 * (I b).card)).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih (fun b' hb' => hsub b' (List.mem_cons_of_mem _ hb'))]
    congr 1
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub b (List.mem_cons_self ..)),
      Finset.sum_const, smul_eq_mul, mul_comm]

lemma blocks_fst_le : ∀ b ∈ blocks, b.1 ≤ 46 := by decide

lemma blk_subset (m : ℕ) : ∀ b ∈ blocks, blk m b ⊆ range (nOf m + 1) := by
  intro b _ k hk
  simp only [blk, Finset.mem_Icc] at hk
  simp only [Finset.mem_range]
  omega

/-- The block product equals `Π_{k ≤ n} x_k^{B_k}`. -/
lemma prod_blocks {M : Type*} [CommMonoid M] (m : ℕ) (x : ℕ → M) :
    (blocks.map (fun b => (∏ k ∈ blk m b, x k) ^ b.2)).prod
      = ∏ k ∈ range (nOf m + 1), x k ^ Bk m k := by
  rw [prod_list_blocks x (blk m) _ blocks (blk_subset m)]
  simp only [Bk_eq]

lemma list_sum_ite_le (L : List (ℕ × ℕ)) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (L.map (fun b => if P b then b.2 else 0)).sum ≤ (L.map Prod.snd).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons]
    have : (if P b then b.2 else 0) ≤ b.2 := by split_ifs <;> omega
    omega

/-- `B_k ≤ S = 35`. -/
lemma Bk_le (m k : ℕ) : Bk m k ≤ 35 := by
  rw [Bk, ← S_eq]
  exact list_sum_ite_le blocks _

/-- `B_k ≥ 8` for `k ≤ n` (the `δ = 0` block covers everything). -/
lemma Bk_ge (m k : ℕ) (hk : k ≤ nOf m) : 8 ≤ Bk m k := by
  rw [Bk, show blocks = (0, 8) :: blocks.tail from rfl, List.map_cons, List.sum_cons]
  have : (if 3 * (0, 8).1 * (m + 1) ≤ k ∧ k ≤ nOf m - 3 * (0, 8).1 * (m + 1) then (0, 8).2
      else 0) = 8 := by simp [hk]
  omega

/-- Mirror symmetry of the block counts: `B_{n-k} = B_k`. -/
lemma Bk_mirror (m k : ℕ) (hk : k ≤ nOf m) : Bk m (nOf m - k) = Bk m k := by
  rw [Bk_eq, Bk_eq]
  congr 1
  refine List.map_congr_left (fun b hb => ?_)
  have h46 := blocks_fst_le b hb
  have hn : nOf m = 480 * (m + 1) := rfl
  have hiff : nOf m - k ∈ blk m b ↔ k ∈ blk m b := by
    have hq : 3 * b.1 * (m + 1) ≤ nOf m := by rw [hn]; nlinarith
    simp only [blk, Finset.mem_Icc]
    generalize 3 * b.1 * (m + 1) = q at *
    omega
  simp only [hiff]

/-- `Σ_{k ≤ n} B_k = 13392(m+1) + 35`. -/
lemma sum_Bk (m : ℕ) : ∑ k ∈ range (nOf m + 1), Bk m k = 13392 * (m + 1) + 35 := by
  simp only [Bk_eq]
  rw [sum_list_blocks (blk m) _ blocks (blk_subset m)]
  simp only [blocks, blk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.card_Icc,
    nOf]
  omega

end BetaIrr.I3
