/-
# Lemma 4 for instance I3: the fields `D`, `D_pos`, `int_ρ`, `int_τ` of `I3.Hyp`, and the
# decomposition of `log D_n - G log n!` by prime ranges

* `D_pos_I3`, `int_rho_I3`, `int_tau_I3`: exactly the forms of the `I3.Hyp` fields
  (`BetaIrrational/FamilyI3.lean`) with `ρ = (pf m).rho`, `τ m j = (pf m).tau (2j-2)`, and
  `D = BetaIrr.I3.Arith.D`. `int_rho_I3` uses `pf_R2_inner_zero` (`I3/Concrete/Expansion.lean`)
  for Lemma C.
* `log_D_sub_eq`: `log D_n - G log n! = Σ_{p ≤ 2n+1} (E_p - G v_p(n!)) log p`.
* `log_D_sub_le`: the explicit split
  `log D_n - G log n! ≤ (20n + 40 + 123(⌊log₂ n⌋+1)) log 2 + 312 ⌊√𝒩⌋ log 𝒩`
  `                    + Σ_{p prime, p ≤ n, 𝒩 < p²} (Esharp_p - G ⌊n/p⌋) log p`,
  where the last sum is the one integrated by the A-certificate (Lemma 5).

Status: complete (no `sorry`).
-/
import BetaIrrational.I3.Arith.Integrality
import BetaIrrational.I3.Arith.Size
import BetaIrrational.I3.Concrete.Expansion

set_option linter.unusedSectionVars false

namespace BetaIrr.I3.Arith

open Finset BetaIrr.Arith

/-! ### Positivity and integrality -/

theorem D_pos_I3 : ∀ m, 0 < D m := D_pos

theorem int_rho_I3 : ∀ m, ∃ z : ℤ, (z : ℚ) = D m * (pf m).rho :=
  fun m => int_rho m (pf_R2_inner_zero m)

theorem int_tau_I3 : ∀ m j, ∃ z : ℤ, (z : ℚ) = D m * (pf m).tau (2 * j - 2) :=
  fun m j => int_tau m (2 * j - 2)

/-! ### `log D_n - G log n!` as a sum over primes -/

/-- The primes `p ≤ 2n+1`. -/
def primesD (m : ℕ) : Finset ℕ := (range (2 * nOf m + 2)).filter Nat.Prime

theorem log_D_eq (m : ℕ) :
    Real.log ((D m : ℚ) : ℝ) = ∑ p ∈ primesD m, (Ep m p : ℝ) * Real.log p := by
  unfold D
  rw [Rat.cast_prod, Real.log_prod (fun p hp => by
    have := (mem_filter.mp hp).2.pos
    push_cast; exact zpow_ne_zero _ (by exact_mod_cast this.ne'))]
  refine sum_congr rfl (fun p _ => ?_)
  push_cast
  rw [Real.log_zpow]

theorem padicValNat_factorial_of_lt {p n : ℕ} (hp : p.Prime) (h : n < p) :
    padicValNat p n.factorial = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun hd => absurd ((Nat.Prime.dvd_factorial hp).mp hd) (by omega))

theorem log_factorial_eq (m : ℕ) :
    Real.log ((nOf m).factorial : ℝ)
      = ∑ p ∈ primesD m, (padicValNat p (nOf m).factorial : ℝ) * Real.log p := by
  set N := (nOf m).factorial
  have hN : N ≠ 0 := Nat.factorial_ne_zero _
  have h1 := Nat.prod_pow_prime_padicValNat N hN (N + 2 * nOf m + 2) (by omega)
  have h2 : ∏ p ∈ primesD m, p ^ padicValNat p N
      = ∏ p ∈ (range (N + 2 * nOf m + 2)).filter Nat.Prime, p ^ padicValNat p N := by
    refine prod_subset (fun p hp => ?_) (fun p hp hnot => ?_)
    · simp only [primesD, mem_filter, mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
    · simp only [primesD, mem_filter, mem_range, not_and] at hp hnot
      have hlt : nOf m < p := by
        by_contra hc; exact hnot (by omega) hp.2
      rw [padicValNat_factorial_of_lt hp.2 hlt, pow_zero]
  rw [h1] at h2
  have h3 : (N : ℝ) = ((∏ p ∈ primesD m, p ^ padicValNat p N : ℕ) : ℝ) := by rw [h2]
  push_cast at h3
  rw [h3, Real.log_prod (fun p hp => by
    have := (mem_filter.mp hp).2.pos
    exact pow_ne_zero _ (by exact_mod_cast this.ne'))]
  refine sum_congr rfl (fun p _ => ?_)
  rw [Real.log_pow]

theorem log_D_sub_eq (m : ℕ) :
    Real.log ((D m : ℚ) : ℝ) - (G : ℝ) * Real.log ((nOf m).factorial : ℝ)
      = ∑ p ∈ primesD m,
          ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p := by
  rw [log_D_eq, log_factorial_eq, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl (fun p _ => ?_)
  ring

/-- For `n < p²`, `v_p(n!) = ⌊n/p⌋`. -/
theorem padicValNat_factorial_of_sq {p n : ℕ} (hp : p.Prime) (h : n < p ^ 2) :
    padicValNat p n.factorial = n / p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_factorial (b := 2)]
  · simp
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · exact Nat.log_lt_of_lt_pow (by omega) h

/-- **The split of `log D_n - G log n!`.** The sharp range `√𝒩 < p ≤ n` is left as the sum that
Lemma 5 (the A-certificate) bounds; the primes `p > n` contribute nothing; `p = 2` and the
small odd primes are bounded explicitly. -/
theorem log_D_sub_le (m : ℕ) :
    Real.log ((D m : ℚ) : ℝ) - (G : ℝ) * Real.log ((nOf m).factorial : ℝ)
      ≤ (20 * (nOf m : ℝ) + 40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1)) * Real.log 2
        + 312 * (Nat.sqrt (NN m) : ℝ) * Real.log (NN m)
        + ∑ p ∈ (primesD m).filter (fun p => p ≤ nOf m ∧ NN m < p ^ 2),
            ((Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)) * Real.log p := by
  rw [log_D_sub_eq]
  set f : ℕ → ℝ := fun p =>
    ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p with hf
  -- split off `p = 2`
  have h2mem : 2 ∈ primesD m := by
    simp only [primesD, mem_filter, mem_range]; exact ⟨by unfold nOf; omega, Nat.prime_two⟩
  rw [← add_sum_erase _ _ h2mem]
  -- the remaining odd primes: small, sharp, and `> n`
  set T := (primesD m).erase 2
  have hsplit : ∑ p ∈ T, f p = ∑ p ∈ T.filter (fun p => p ^ 2 ≤ NN m), f p
      + ∑ p ∈ T.filter (fun p => ¬ p ^ 2 ≤ NN m), f p := (sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit]
  -- `p = 2`
  have hE2 : f 2 ≤ (20 * (nOf m : ℝ) + 40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1)) * Real.log 2 := by
    simp only [hf]
    have h := E2_sub_le m
    have hEp : Ep m 2 = E2 m := by simp [Ep]
    rw [hEp]
    have hR : ((E2 m : ℝ) - (G : ℝ) * (padicValNat 2 (nOf m).factorial : ℝ))
        ≤ 20 * (nOf m : ℝ) + 40 + 123 * ((Nat.log 2 (nOf m) : ℝ) + 1) := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_right hR (Real.log_nonneg (by norm_num))
  -- small odd primes
  have hsmall : ∑ p ∈ T.filter (fun p => p ^ 2 ≤ NN m), f p
      ≤ 312 * (Nat.sqrt (NN m) : ℝ) * Real.log (NN m) := by
    refine le_trans (le_of_eq ?_) (small_primes_sum_le m)
    refine sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [T, primesD, mem_filter, mem_erase, mem_range, mem_Icc]
    constructor
    · rintro ⟨⟨hp2, _, hpP⟩, hpN⟩
      exact ⟨⟨by have := hpP.two_le; omega, Nat.le_sqrt'.mpr hpN⟩, hpP⟩
    · rintro ⟨⟨hp3, hpS⟩, hpP⟩
      have hpN := Nat.le_sqrt'.mp hpS
      refine ⟨⟨by omega, ?_, hpP⟩, hpN⟩
      unfold NN at hpN; unfold nOf
      by_contra hc
      nlinarith
  -- large odd primes: `p > n` contribute `0`, the rest is the sharp sum
  have hlarge : ∑ p ∈ T.filter (fun p => ¬ p ^ 2 ≤ NN m), f p
      = ∑ p ∈ (primesD m).filter (fun p => p ≤ nOf m ∧ NN m < p ^ 2),
          ((Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)) * Real.log p := by
    rw [← sum_filter_add_sum_filter_not (T.filter (fun p => ¬ p ^ 2 ≤ NN m))
      (fun p => p ≤ nOf m)]
    have hzero : ∑ p ∈ (T.filter (fun p => ¬ p ^ 2 ≤ NN m)).filter (fun p => ¬ p ≤ nOf m), f p
        = 0 := by
      refine sum_eq_zero (fun p hp => ?_)
      simp only [T, primesD, mem_filter, mem_erase, mem_range] at hp
      have hlt : nOf m < p := by omega
      simp only [hf, Ep_eq_zero_of_lt hp.1.1.1 hlt, padicValNat_factorial_of_lt hp.1.1.2.2 hlt]
      simp
    rw [hzero, add_zero]
    refine sum_congr ?_ (fun p hp => ?_)
    · ext p
      simp only [T, primesD, mem_filter, mem_erase, mem_range]
      constructor
      · rintro ⟨⟨⟨_, h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, h4, by omega⟩
      · rintro ⟨⟨h1, h2⟩, h4, h5⟩
        exact ⟨⟨⟨by rintro rfl; unfold NN at h5; omega, h1, h2⟩, by omega⟩, h4⟩
    · simp only [primesD, mem_filter, mem_range] at hp
      have hp2 : p ≠ 2 := by rintro rfl; unfold NN at hp; omega
      have hpn : ¬ nOf m < p := by omega
      have hEp : Ep m p = Esharp m p := by simp [Ep, hp2, hpn, hp.2.2]
      have hv : padicValNat p (nOf m).factorial = nOf m / p :=
        padicValNat_factorial_of_sq hp.1.2 (lt_trans (nOf_lt_NN m) hp.2.2)
      simp only [hf, hEp, hv]
  rw [hlarge]
  have hf2 : f 2 = ((Ep m 2 : ℝ) - (G : ℝ) * (padicValNat 2 (nOf m).factorial : ℝ))
      * Real.log ((2 : ℕ) : ℝ) := rfl
  rw [← hf2]
  have := add_le_add hE2 (add_le_add hsmall (le_refl (∑ p ∈ (primesD m).filter
    (fun p => p ≤ nOf m ∧ NN m < p ^ 2),
      ((Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)) * Real.log p)))
  linarith

end BetaIrr.I3.Arith
