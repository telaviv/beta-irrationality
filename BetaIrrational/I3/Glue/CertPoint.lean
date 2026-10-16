/-
# Glue (I3): Lemma 5 (a) for the exponent `Arith.Esharp`, from `CertA.pointwise_le_eStar_prime`

Here `Arith` is `BetaIrr.I3.Arith` and `CertA` is `BetaIrr.I3.CertA`.

The two files define `c_p(k)` and `P_{p,j}(k)` separately: `Arith.cp ≥ CertA.cp` (Arith also
counts the `e`-factor) and `Arith.Ppj = CertA.Ppj`.

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.CertA.Pointwise
import BetaIrrational.I3.Arith.Ep

namespace BetaIrr.I3

open Finset

/-! ### (a) the pointwise bound for the exponent `Arith.Esharp` -/

lemma cp_le (m p k : ℕ) : ((CertA.cp m p k : ℕ) : ℤ) ≤ Arith.cp m p k := by
  unfold CertA.cp Arith.cp
  have e : ((3 * #{l ∈ Icc (-(1040 * ((m : ℤ) + 1)) - 1) (560 * ((m : ℤ) + 1)) |
      (p : ℤ) ∣ 2 * (k : ℤ) + 1 + 2 * l} : ℕ) : ℤ) =
      ∑ l ∈ Arith.zeroSet m, 3 * (if (p : ℤ) ∣ Arith.wl k l then 1 else 0) := by
    rw [← mul_sum, sum_boole]
    push_cast
    rfl
  rw [e]
  have : (0 : ℤ) ≤ if (p : ℤ) ∣ (nOf m : ℤ) - 2 * k then 1 else 0 := by split_ifs <;> norm_num
  linarith

lemma Ppj_eq (m p k : ℕ) (b : ℕ × ℕ) : Arith.Ppj m p k b = CertA.Ppj m p b.1 k := by
  unfold Arith.Ppj CertA.Ppj Arith.blockSet
  refine Finset.card_bij (fun a _ => (a : ℤ)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_erase, mem_Icc] at ha ⊢
    refine ⟨⟨by exact_mod_cast ha.1.1, by exact_mod_cast ha.1.2.1, by exact_mod_cast ha.1.2.2⟩,
      ha.2⟩
  · intro a _ b _ h; exact_mod_cast h
  · intro z hz
    simp only [mem_filter, mem_erase, mem_Icc] at hz
    refine ⟨z.toNat, ?_, by omega⟩
    simp only [mem_filter, mem_erase, mem_Icc]
    refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]; exact hz.2

lemma Bk_pos (m k : ℕ) (hk : k ≤ nOf m) : 1 ≤ Bk m k :=
  le_trans (by norm_num) (Bk_ge m k hk)

/-- **Lemma 5 (a) for the exponent `Arith.Esharp`.** For primes `p ≤ n` with `𝒩 < p²`:
`E_p - G⌊n/p⌋ ≤ e*(n/p)`. -/
theorem Esharp_sub_le_eStar (m p : ℕ) (hp : p.Prime) (hpn : p ≤ nOf m)
    (hN : Arith.NN m < p ^ 2) :
    (Arith.Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ) ≤
      ((CertA.eStar ((nOf m : ℚ) / p) : ℚ) : ℝ) := by
  have hp2 : p ≠ 2 := by rintro rfl; unfold Arith.NN at hN; omega
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (s := range (nOf m + 1))
    Finset.nonempty_range_add_one (fun k => (Bk m k : ℤ) + 2 - Arith.eSharp m p k)
  have hE : Arith.Esharp m p = (Bk m k : ℤ) + 2 - Arith.eSharp m p k := hkeq
  have hkn : k ≤ nOf m := by rw [mem_range] at hk; omega
  have hpt := CertA.pointwise_le_eStar_prime m p k hp hp2 hpn (Bk_pos m k hkn)
  have hfl : ⌊(nOf m : ℚ) / p⌋ = ((nOf m / p : ℕ) : ℤ) := by
    rw [Rat.floor_natCast_div_natCast]; push_cast; rfl
  rw [hfl] at hpt
  have hsum : (blocks.map fun b => (b.2 : ℤ) * Arith.Ppj m p k b).sum =
      (blocks.map fun b => (b.2 : ℤ) * (CertA.Ppj m p b.1 k : ℤ)).sum := by
    exact congrArg List.sum (List.map_congr_left (fun b _ => by rw [Ppj_eq]))
  have hcp := cp_le m p k
  have hE' : Arith.Esharp m p ≤ (Bk m k : ℤ) + 2 - (CertA.cp m p k : ℤ) +
      (blocks.map fun b => (b.2 : ℤ) * (CertA.Ppj m p b.1 k : ℤ)).sum := by
    rw [hE, Arith.eSharp_eq, hsum]; linarith
  have hE'' : (Arith.Esharp m p : ℚ) - G * ((nOf m / p : ℕ) : ℚ) ≤
      CertA.eStar ((nOf m : ℚ) / p) := by
    have : (Arith.Esharp m p : ℚ) ≤ (Bk m k : ℚ) + 2 - (CertA.cp m p k : ℚ) +
        (((blocks.map fun b => (b.2 : ℤ) * (CertA.Ppj m p b.1 k : ℤ)).sum : ℤ) : ℚ) := by
      exact_mod_cast hE'
    rw [Int.cast_natCast] at hpt
    linarith
  exact_mod_cast hE''

end BetaIrr.I3
